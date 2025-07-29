use aig::Aig;
use clap::Parser;
use rIC3::{frontend::aig::aig_preprocess, transys::Transys};
use serde::Deserialize;

#[derive(Deserialize)]
#[allow(dead_code)]
struct YWAMap {
    asserts: Vec<[String; 1]>,
    assumes: Vec<[String; 1]>,
}

#[derive(clap::Parser, Debug)]
struct Args {
    aig: String,
    out: String,

    #[clap(subcommand)]
    sub: Subcommand,
}

#[derive(clap::Subcommand, Debug)]
enum Subcommand {
    Select {
        ywa: String,
        step: usize,
        prop: Vec<String>,
    },
    Optimise,
}

fn main() {
    let args = Args::parse();
    println!("{:?}", args);

    let aig = aig::Aig::from_file(&args.aig);
    let (mut aig, _) = rIC3::frontend::aig::aig_preprocess(&aig);

    match args.sub {
        Subcommand::Select { ywa, step, prop } => {
            let ywamap: YWAMap = serde_json::from_reader(std::io::BufReader::new(
                std::fs::OpenOptions::new()
                    .read(true)
                    .open(&ywa)
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
                let (stepn, name) = name.split_once('_').expect("badly formed property");
                assert!(stepn.starts_with("Step"));
                let pstep: usize = stepn[4..].parse().expect("badly formed property name");

                if pstep < step {
                    println!("Assert2Assume {}", name);
                    aig.constraints.push(!aig.bads[b]);
                    aig.bads.remove(b);
                } else if pstep == step && (prop.is_empty() || prop.iter().any(|x| x == name)) {
                    println!("Keeping {}", name);
                    b += 1;
                } else {
                    println!("Deleting {}", name);
                    aig.bads.remove(b);
                }
                bn += 1;
            }
        }
        Subcommand::Optimise => {
            println!(
                "WARNING: This has been observed to produce bigger results that are simply slower to manipulate. You probably don't want that!"
            );
            let _ots = Transys::from_aig(&aig, true);
            let (aign, mut rst) = aig_preprocess(&aig);
            let mut ts = Transys::from_aig(&aign, true);
            ts.simplify(&mut rst);
            aig = Aig::from(&ts);
        }
    }

    aig.to_file(&args.out, false);
}
