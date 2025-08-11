use std::collections::HashSet;
use std::fmt::Write;
use std::{
    collections::HashMap,
    io::{BufReader, BufWriter},
};

use aig::{AigEdge, TernarySimulate};
use clap::Parser;
use serde::Deserialize;

#[derive(Deserialize, Debug)]
#[allow(dead_code)]
struct YWAInput {
    input: usize,
    offset: usize,
    path: [String; 1],
}

#[derive(Deserialize)]
#[allow(dead_code)]
struct YWAMap {
    asserts: Vec<[String; 1]>,
    assumes: Vec<[String; 1]>,
    inputs: Vec<YWAInput>,
    seqs: Vec<YWAInput>,
    inits: Vec<YWAInput>,
}

impl YWAMap {
    pub fn parse(reader: impl std::io::BufRead) -> YWAMap {
        serde_json::from_reader(reader).expect("Could not parse YWA json")
    }

    fn decode_name(s: &str) -> &str {
        let (_, chunk) = s.rsplit_once('.').unwrap_or(("", s));
        let (chunk, _) = chunk.split_once('$').unwrap_or((chunk, ""));
        chunk
    }

    pub fn vmap_wires(&self, aig: &aig::Aig) -> impl Iterator<Item = VMapWire> {
        self.asserts
            .iter()
            .enumerate()
            .map(|(i, x)| (aig.bads[i], x))
            .map(|(i, x)| VMapWire {
                index: (i.node_id() << 1) | (!i.compl() as usize),
                offset: 0,
                path: YWAMap::decode_name(&x[0]).to_string(),
            })
            .chain(
                self.assumes
                    .iter()
                    .enumerate()
                    .map(|(i, x)| (aig.constraints[i], x))
                    .map(|(i, x)| VMapWire {
                        index: (i.node_id() << 1) | (i.compl() as usize),
                        offset: 0,
                        path: YWAMap::decode_name(&x[0]).to_string(),
                    }),
            )
    }
}

#[derive(Debug)]
struct VMapWire {
    index: usize,
    offset: usize,
    path: String,
}

impl VMapWire {
    pub fn aig_edge(&self) -> AigEdge {
        AigEdge::new(self.index >> 1, self.index & 1 != 0)
    }
}

#[derive(Debug)]
struct VMapWireGroup<'a> {
    path: &'a str,
    own_name: &'a str,
    /// Bits are ordered MSB to LSB
    bits: Vec<&'a VMapWire>,
}

impl<'a> VMapWireGroup<'a> {
    pub fn aig_edges(&self) -> impl Iterator<Item = AigEdge> {
        self.bits.iter().map(|x| x.aig_edge())
    }
}

#[derive(Debug)]
struct WireHierarchy<'a> {
    wires: Vec<VMapWireGroup<'a>>,
    modules: HashMap<&'a str, WireHierarchy<'a>>,
}

#[derive(Debug)]
struct WireExtractionInstruction<'a> {
    group: &'a VMapWireGroup<'a>,
    edges: Vec<AigEdge>,
    idcode: vcd::IdCode,
}

impl<'a> WireHierarchy<'a> {
    pub fn walk<F: FnMut(&'a VMapWireGroup<'a>)>(&'a self, f: &mut F) {
        for group in &self.wires {
            f(group);
        }
        for (_, module) in self.modules.iter() {
            module.walk(f);
        }
    }

    pub fn find(&self, path: &[&str]) -> Option<&VMapWireGroup<'a>> {
        if path.len() == 1 {
            return self.wires.iter().find(|x| x.own_name == path[0]);
        }
        self.modules.get(path[0])?.find(&path[1..])
    }

    pub fn append_to_vcd(
        &'a self,
        vcd: &mut vcd::Writer<impl std::io::Write>,
        extraction: &mut Vec<WireExtractionInstruction<'a>>,
    ) -> std::io::Result<()> {
        for wire in &self.wires {
            let idcode = vcd.add_wire(wire.bits.len() as u32, wire.own_name)?;
            extraction.push(WireExtractionInstruction {
                group: wire,
                edges: wire.aig_edges().collect(),
                idcode,
            });
        }

        for (name, module) in &self.modules {
            vcd.add_module(name)?;
            module.append_to_vcd(vcd, extraction)?;
            vcd.upscope()?;
        }
        Ok(())
    }

    pub fn named_aiger_vars(&self) -> HashMap<usize, &'a VMapWireGroup<'_>> {
        let mut named_wires = HashMap::new();
        self.walk(&mut |group| {
            for bit in &group.bits {
                named_wires.insert(bit.index >> 1, group);
            }
        });
        named_wires
    }
}

struct VMap {
    wires: Vec<VMapWire>,
}

impl VMap {
    pub fn parse(reader: impl std::io::BufRead) -> VMap {
        let mut vmap = VMap { wires: Vec::new() };
        for line in reader.lines() {
            let line = line.expect("read failed");
            if line.starts_with("wire ") {
                let [index, offset, name] = line[5..]
                    .splitn(3, " ")
                    .collect::<Vec<_>>()
                    .try_into()
                    .expect("malformed vmap");
                if !name.starts_with("$") {
                    vmap.wires.push(VMapWire {
                        // index: (index.parse::<usize>().expect("expected number") >> 1) - 1,
                        index: index.parse::<usize>().expect("expected number"),
                        offset: offset.parse().expect("expected number"),
                        path: name.to_string(),
                    })
                }
            }
        }
        vmap
    }

    pub fn to_hierarchy(&'_ self) -> WireHierarchy<'_> {
        fn to_hierarchy_from<'a>(wires: &[&'a VMapWire], depth: usize) -> WireHierarchy<'a> {
            let mut new_wires = HashMap::<_, Vec<_>>::new();
            let mut modules = HashMap::<_, Vec<_>>::new();

            for wire in wires {
                if wire.path.starts_with("$") {
                    continue;
                }
                let mut split = wire.path.splitn(depth + 2, ".").skip(depth);
                let fst = split.next().expect("name too short?");
                let snd = split.next();
                if let Some(_) = snd {
                    modules.entry(fst).or_default().push(*wire);
                } else {
                    new_wires.entry(wire.path.as_str()).or_default().push(*wire);
                }
            }

            WireHierarchy {
                wires: new_wires
                    .into_iter()
                    .map(|(path, mut bits)| {
                        bits.sort_by(|a, b| b.offset.cmp(&a.offset));
                        let own_name = match path.rsplit_once('.') {
                            None => path,
                            Some((_, name)) => name,
                        };
                        VMapWireGroup {
                            path,
                            own_name,
                            bits,
                        }
                    })
                    .collect(),
                modules: modules
                    .into_iter()
                    .map(|(name, wires)| (name, to_hierarchy_from(&wires, depth + 1)))
                    .collect(),
            }
        }

        to_hierarchy_from(&self.wires.iter().collect::<Vec<_>>(), 0)
    }
}

#[derive(Clone, Debug)]
struct BitVec {
    len: usize,
    inner: Vec<u64>,
}

impl BitVec {
    pub fn new() -> BitVec {
        BitVec {
            len: 0,
            inner: Vec::new(),
        }
    }

    pub fn fill_zero(len: usize) -> BitVec {
        BitVec {
            len,
            inner: vec![0; len.div_ceil(64)],
        }
    }

    pub fn set(&mut self, idx: usize, value: bool) {
        assert!(idx < self.len);
        if value {
            self.inner[idx / 64] |= 1 << (idx % 64);
        } else {
            self.inner[idx / 64] &= !(1 << (idx % 64));
        }
    }

    pub fn push(&mut self, value: bool) {
        if self.len % 64 == 0 {
            self.inner.push(value as u64);
        } else {
            *self.inner.last_mut().unwrap() |= (value as u64) << (self.len % 64);
        }
        self.len += 1;
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if index >= self.len {
            None
        } else {
            Some((self.inner[index / 64] >> (index % 64)) & 1 != 0)
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = bool> {
        (0..self.len).map(|x| self.get(x).unwrap())
    }
}

impl FromIterator<bool> for BitVec {
    fn from_iter<T: IntoIterator<Item = bool>>(iter: T) -> Self {
        let mut vec = BitVec::new();
        for item in iter {
            vec.push(item);
        }
        vec
    }
}

struct AigerWitness {
    initial_state: BitVec,
    inputs: Vec<BitVec>,
}

impl AigerWitness {
    pub fn parse(reader: impl std::io::BufRead) -> std::io::Result<AigerWitness> {
        let mut witness = AigerWitness {
            initial_state: BitVec::new(),
            inputs: Vec::new(),
        };

        let mut lines = reader.lines();
        assert_eq!(lines.next().expect("malformed witness file")?.as_str(), "1");
        lines.next().expect("malformed witness file")?;

        witness.initial_state = lines
            .next()
            .expect("malformed witness file")?
            .chars()
            .map(|c| match c {
                '0' => false,
                '1' => true,
                _ => panic!(),
            })
            .collect();

        while let line = lines.next().expect("malformed witness file")?
            && line != "."
        {
            witness.inputs.push(
                line.chars()
                    .map(|c| match c {
                        '0' => false,
                        '1' => true,
                        _ => panic!(),
                    })
                    .collect(),
            );
        }

        Ok(witness)
    }

    pub fn simulate_to_step<'a>(&self, aig: &'a aig::Aig, step: usize) -> TernarySimulate<'a> {
        let mut sim =
            TernarySimulate::new(&aig, self.initial_state.iter().map(|x| x.into()).collect());
        for step in self.inputs.iter().take(step) {
            sim.simulate(step.iter().map(|x| x.into()).collect());
        }
        sim
    }
}

pub fn check_aig(aig: &aig::Aig) {
    let mut ok = BitVec::fill_zero(aig.nodes.len());
    ok.set(0, true);
    for i in 0..aig.inputs.len() {
        ok.set(aig.inputs[i], true);
    }
    for i in 0..aig.latchs.len() {
        ok.set(aig.latchs[i].input, true);
    }
    for i in aig.nodes_range() {
        if aig.nodes[i].is_and() {
            assert!(ok.get(aig.nodes[i].fanin0().node_id()).unwrap());
            assert!(ok.get(aig.nodes[i].fanin1().node_id()).unwrap());
            ok.set(i, true);
        }
    }
    for i in 0..aig.latchs.len() {
        assert!(ok.get(aig.latchs[i].next.node_id()).unwrap());
    }
}

#[derive(clap::Parser, Debug)]
struct Args {
    aig: String,

    #[clap(subcommand)]
    sub: Subcommand,
}

#[derive(clap::Subcommand, Debug)]
enum Subcommand {
    Select {
        #[clap(long)]
        no_assumes: bool,
        out: String,
        ywa: String,
        step: usize,
        prop: Vec<String>,
    },
    Simulate {
        ywa: String,
        vmap: String,
        trace: String,
        vcd: String,
    },
    Coi {
        vmap: String,
        name: String,
        #[clap(long)]
        ywmap: Option<String>,
    },
    SpecInputs {
        vmap: String,
        trace: String,
        out: String,
        step: usize,
    },
    Why {
        vmap: String,
        trace: String,
        step: usize,
        signal: String,
        #[clap(long, short)]
        bit: Option<usize>,
    },
}

fn select(
    mut aig: aig::Aig,
    out: String,
    ywa: String,
    step: usize,
    prop: Vec<String>,
    no_assumes: bool,
) {
    let ywamap = YWAMap::parse(BufReader::new(
        std::fs::File::open(&ywa).expect("Could not open YWA file"),
    ));

    assert_eq!(aig.justice.len(), 0);
    assert_eq!(aig.fairness.len(), 0);

    assert_eq!(aig.bads.len(), ywamap.asserts.len());

    let mut bn = 0;
    let mut b = 0;
    while b < aig.bads.len() {
        let name = &ywamap.asserts[bn][0][6..]
            .split_once('$')
            .expect("Expected \\top.*$n")
            .0;
        bn += 1;
        let (stepn, name) = name.split_once('_').expect("badly formed property");
        assert!(stepn.starts_with("Step"));
        let pstep: usize = stepn[4..].parse().expect("badly formed property name");

        let is_cover = name.ends_with("_Cover");

        if pstep == step && (prop.is_empty() || prop.iter().any(|x| x == name)) {
            if is_cover {
                println!("Keeping {name} (cover statement, negating)");
                aig.bads[b] = !aig.bads[b];
            } else {
                println!("Keeping {name}");
            }
            b += 1;
        } else if no_assumes || is_cover || pstep >= step {
            println!("Deleting {}", name);
            aig.bads.remove(b);
        } else if pstep < step {
            println!("Assert2Assume {}", name);
            aig.constraints.push(!aig.bads[b]);
            aig.bads.remove(b);
        } else {
            panic!()
        }
    }

    aig.to_file(&out, false);
}

fn simulate(aig: aig::Aig, ywa: String, vmap: String, trace: String, out: String) {
    let ywamap = YWAMap::parse(BufReader::new(
        std::fs::File::open(&ywa).expect("Could not open YWA file"),
    ));
    let mut vmap = VMap::parse(BufReader::new(
        std::fs::File::open(vmap).expect("Could not open vmap"),
    ));
    vmap.wires.extend(ywamap.vmap_wires(&aig));

    let mut vcd = vcd::Writer::new(BufWriter::new(
        std::fs::OpenOptions::new()
            .write(true)
            .create(true)
            .truncate(true)
            .open(out)
            .expect("Could not open VCD out"),
    ));
    vcd.timescale(1, vcd::TimescaleUnit::US).unwrap();

    let hier = vmap.to_hierarchy();
    let mut extract = Vec::new();
    vcd.add_module("top").unwrap();
    hier.append_to_vcd(&mut vcd, &mut extract)
        .expect("Could not write wire hierarchy to VCD");
    vcd.upscope().unwrap();
    vcd.enddefinitions().unwrap();

    let witness = AigerWitness::parse(BufReader::new(
        std::fs::File::open(&trace).expect("could not open witness file"),
    ))
    .expect("error reading witness file");

    let mut sim = TernarySimulate::new(
        &aig,
        witness.initial_state.iter().map(|x| x.into()).collect(),
    );
    for (s, step) in witness.inputs.iter().enumerate() {
        sim.simulate(step.iter().map(|x| x.into()).collect());
        println!("Step {}", s);

        for (a, [assert]) in ywamap.asserts.iter().enumerate() {
            if assert.contains("_Cover") {
                continue;
            }
            if sim.value(aig.bads[a]).is_true() {
                println!("Violated assertion {assert}");
            }
        }
        for (a, [assume]) in ywamap.assumes.iter().enumerate() {
            if sim.value(aig.constraints[a]).is_false() {
                println!("Violated assumption {assume}");
            }
        }

        vcd.timestamp(s as u64).unwrap();
        for instr in &extract {
            let bits: Vec<_> = instr
                .edges
                .iter()
                .map(|edge| {
                    let v = sim.value(*edge);
                    if v.is_true() {
                        vcd::Value::V1
                    } else if v.is_false() {
                        vcd::Value::V0
                    } else {
                        vcd::Value::X
                    }
                })
                .collect();
            if let [bit] = &bits[..] {
                vcd.change_scalar(instr.idcode, *bit).unwrap();
            } else {
                vcd.change_vector(instr.idcode, bits).unwrap();
            }
        }
    }
    vcd.timestamp(witness.inputs.len() as u64).unwrap();
}

fn coi(aig: aig::Aig, vmap: String, signal: String, ywmap: Option<String>) {
    let mut vmap = VMap::parse(BufReader::new(
        std::fs::File::open(vmap).expect("Could not open vmap"),
    ));
    if let Some(ywmap) = ywmap {
        let ywamap = YWAMap::parse(BufReader::new(
            std::fs::File::open(&ywmap).expect("Could not open YWA file"),
        ));
        vmap.wires.extend(ywamap.vmap_wires(&aig));
    }
    let hier = vmap.to_hierarchy();
    let group = hier.find(&signal.split(".").collect::<Vec<_>>());
    let Some(group) = group else {
        println!("Name not found");
        return;
    };

    let named_wires = hier.named_aiger_vars();
    let mut found = HashSet::new();
    let mut visited = HashSet::new();

    for bit in &group.bits {
        let node = &aig.nodes[bit.index >> 1];
        if !node.is_and() {
            continue;
        }
        let mut to_visit = vec![node.fanin0().node_id(), node.fanin1().node_id()];
        while let Some(nodeid) = to_visit.pop() {
            if let Some(wire) = named_wires.get(&nodeid) {
                found.insert((wire.path, node.is_and()));
                continue;
            }
            let node = &aig.nodes[nodeid];
            if !node.is_and() {
                continue;
            }
            if visited.insert(node.fanin0()) {
                to_visit.push(node.fanin0().node_id());
            }
            if visited.insert(node.fanin1()) {
                to_visit.push(node.fanin1().node_id());
            }
        }
    }

    for (found, and) in found {
        if and {
            println!("{} (and node)", found);
        } else {
            println!("{}", found);
        }
    }
}

fn why(
    aig: aig::Aig,
    vmap: String,
    trace: String,
    step: usize,
    signal: String,
    bit: Option<usize>,
) {
    let vmap = VMap::parse(BufReader::new(
        std::fs::File::open(vmap).expect("Could not open vmap"),
    ));

    let hier = vmap.to_hierarchy();
    let group = hier.find(&signal.split(".").collect::<Vec<_>>());
    let Some(group) = group else {
        println!("Name not found");
        return;
    };

    let witness = AigerWitness::parse(BufReader::new(
        std::fs::File::open(&trace).expect("could not open witness file"),
    ))
    .expect("error reading witness file");
    let sim = witness.simulate_to_step(&aig, step);

    let named_wires = hier.named_aiger_vars();
    let mut found = HashMap::new();
    let mut visited = HashSet::new();

    let bits = match bit {
        None => &group.bits[..],
        Some(i) => &[group.bits[i]],
    };
    for bit in bits {
        let node = &aig.nodes[bit.index >> 1];
        if !node.is_and() {
            continue;
        }
        let mut to_visit = vec![
            (node.fanin0().node_id(), vec![bit.index >> 1]),
            (node.fanin1().node_id(), vec![bit.index >> 1]),
        ];
        while let Some((nodeid, path)) = to_visit.pop() {
            if let Some(wire) = named_wires.get(&nodeid) {
                found.insert(nodeid, (wire.path, wire));
                continue;
            }
            let node = &aig.nodes[nodeid];
            if !node.is_and() {
                continue;
            }
            let left = sim.value(node.fanin0());
            let right = sim.value(node.fanin1());
            assert!(!left.is_none() && !right.is_none());

            let mut new_path = path.clone();
            new_path.push(nodeid);
            match (left.is_true(), right.is_true()) {
                (true, true) | (false, false) => {
                    if visited.insert(node.fanin0().node_id()) {
                        to_visit.push((node.fanin0().node_id(), new_path.clone()));
                    }
                    if visited.insert(node.fanin1().node_id()) {
                        to_visit.push((node.fanin1().node_id(), new_path));
                    }
                }
                (true, false) => {
                    if visited.insert(node.fanin1().node_id()) {
                        to_visit.push((node.fanin1().node_id(), new_path));
                    }
                }
                (false, true) => {
                    if visited.insert(node.fanin0().node_id()) {
                        to_visit.push((node.fanin0().node_id(), new_path));
                    }
                }
            }
        }
    }

    let mut lines = Vec::new();
    for (wirei, (_path, group)) in found.iter() {
        let wire = group.bits.iter().find(|x| x.index >> 1 == *wirei).unwrap();
        let v = sim.value(wire.aig_edge());
        let c = if v.is_true() {
            '1'
        } else if v.is_false() {
            '0'
        } else {
            'x'
        };
        lines.push(format!(
            "{} [{}] = {c}     ({})",
            wire.path,
            wire.offset,
            wire.index,
            // group.aig_edges().map(|x| x.node_id()).collect::<Vec<_>>()
        ));
    }
    lines.sort();
    for line in lines {
        println!("{}", line);
    }
}

fn spec_inputs(aig: aig::Aig, vmap: String, trace: String, out: String, step: usize) {
    let vmap = VMap::parse(BufReader::new(
        std::fs::File::open(vmap).expect("Could not open vmap"),
    ));
    let hier = vmap.to_hierarchy();

    let spec_inputs = hier
        .modules
        .get("spec_api_i")
        .unwrap()
        .modules
        .get("spec_i")
        .unwrap()
        .wires
        .iter()
        .filter(|x| {
            let name = x.path;
            name.ends_with("_in")
                || name.ends_with("_sail_invoke_ret")
                || name.ends_with("insn_bits")
                || name.ends_with("main_mode")
        })
        .collect::<Vec<_>>();
    println!("{:?}", spec_inputs);

    let witness = AigerWitness::parse(BufReader::new(
        std::fs::File::open(&trace).expect("could not open witness file"),
    ))
    .expect("error reading witness file");

    let sim = witness.simulate_to_step(&aig, step);

    let mut spec_bindings = String::new();
    for input in &spec_inputs {
        let bits: String = input
            .aig_edges()
            .map(|edge| {
                let v = sim.value(edge);
                if v.is_true() {
                    '1'
                } else if v.is_false() {
                    '0'
                } else {
                    'x'
                }
            })
            .collect();
        writeln!(
            &mut spec_bindings,
            ".{}({}'b{bits}),",
            input.own_name,
            bits.len(),
        )
        .unwrap();
    }
    std::fs::write(out, spec_bindings).unwrap();
}

fn main() {
    let args = Args::parse();
    println!("{:?}", args);

    let aig = aig::Aig::from_file(&args.aig);
    check_aig(&aig);

    match args.sub {
        Subcommand::Select {
            out,
            ywa,
            step,
            prop,
            no_assumes,
        } => select(aig, out, ywa, step, prop, no_assumes),
        Subcommand::Simulate {
            ywa,
            vmap,
            trace,
            vcd: out,
        } => simulate(aig, ywa, vmap, trace, out),
        Subcommand::Coi { vmap, name, ywmap } => coi(aig, vmap, name, ywmap),
        Subcommand::SpecInputs {
            vmap,
            trace,
            out,
            step,
        } => spec_inputs(aig, vmap, trace, out, step),
        Subcommand::Why {
            vmap,
            trace,
            step,
            signal,
            bit,
        } => why(aig, vmap, trace, step, signal, bit),
    }
}
