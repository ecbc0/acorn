// A representative run of the verifier, to use for profiling.
// This does a reverify run, so you should run it once first to populate the cache.
//
// To profile using samply:
//
//   cargo build --bin=profile_verifier --profile=fastdev
//   samply record target/fastdev/profile_verifier

use acorn::{project::ProjectConfig, verifier::Verifier};
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    for _ in 0..1 {
        let config = ProjectConfig {
            use_certs: true,
            ..Default::default()
        };
        let mut verifier =
            Verifier::new(current_dir.clone(), config, None).expect("Failed to create verifier");
        verifier.builder.check_hashes = false;

        let output = verifier.run().unwrap();
        if !output.status.is_good() {
            println!("exiting.");
            std::process::exit(1);
        }
    }
}
