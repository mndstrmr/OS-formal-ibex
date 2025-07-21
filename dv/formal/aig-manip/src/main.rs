use aig::AigEdge;
use clap::Parser;
use serde::Deserialize;

#[derive(Deserialize)]
struct YWAMap {
    asserts: Vec<[String; 1]>,
    assumes: Vec<[String; 1]>,
}

enum PropertyConfig {
    WholeStep(usize),
    PropertyGroup(usize, Vec<String>),
}

enum AssertAction {
    Delete,
    ToAssume,
    Keep,
}

impl PropertyConfig {
    pub fn action_for(&self, name: &str) -> AssertAction {
        let (stepn, name) = name.split_once('_').expect("badly formed property");
        assert!(stepn.starts_with("Step"));
        let step: usize = stepn[4..].parse().expect("badly formed property name");
        match self {
            PropertyConfig::WholeStep(n) => match step.cmp(n) {
                std::cmp::Ordering::Less => AssertAction::ToAssume,
                std::cmp::Ordering::Equal => AssertAction::Keep,
                std::cmp::Ordering::Greater => AssertAction::Delete,
            },
            PropertyConfig::PropertyGroup(n, items) => match step.cmp(n) {
                std::cmp::Ordering::Less => AssertAction::ToAssume,
                std::cmp::Ordering::Equal if items.iter().any(|x| x == name) => AssertAction::Keep,
                std::cmp::Ordering::Equal | std::cmp::Ordering::Greater => AssertAction::Delete,
            },
        }
    }
}

#[derive(clap::Parser, Debug)]
struct Args {
    aig: String,
    ywa: String,
    step: usize,
    out: String,
    prop: Vec<String>,
}

fn main() {
    let args = Args::parse();
    println!("{:?}", args);

    let conf;
    if args.prop.len() > 0 {
        conf = PropertyConfig::PropertyGroup(args.step, args.prop);
    } else {
        conf = PropertyConfig::WholeStep(args.step);
    }

    let mut aig = aig::Aig::from_file(&args.aig);
    let ywamap: YWAMap = serde_json::from_reader(std::io::BufReader::new(
        std::fs::OpenOptions::new()
            .read(true)
            .open(&args.ywa)
            .expect("Could not open YWA file"),
    ))
    .expect("Could not parse YWA json");

    assert_eq!(aig.justice.len(), 0);
    assert_eq!(aig.fairness.len(), 0);

    let mut bn = 0;
    let mut b = 0;
    while b < aig.bads.len() {
        let name = &ywamap.asserts[bn][0][6..]
            .split_once('$')
            .expect("Expected \\top.*$n")
            .0;
        match conf.action_for(name) {
            AssertAction::Delete => {
                println!("Deleting {}", name);
                aig.bads.remove(b);
            }
            AssertAction::ToAssume => {
                println!("Assert2Assume {}", name);
                let imply = aig.new_imply_node(aig.bads[b], AigEdge::constant(false));
                aig.constraints.push(imply);
                aig.bads.remove(b);
            }
            AssertAction::Keep => {
                println!("Keeping {}", name);
                b += 1;
            }
        }
        bn += 1;
    }

    aig.to_file(&args.out, false);
}
