// A representative run of the reprove command, to use for profiling.
// This reproving the real.double_sum module.
//
// To profile using samply:
//
//   cargo build --bin=profile_reprove --profile=fastdev
//   samply record target/fastdev/profile_reprove

use acorn::{project::ProjectConfig, verifier::Verifier};
use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    for _ in 0..1 {
        let config = ProjectConfig {
            use_filesystem: true,
            read_cache: false,
            write_cache: false,
        };

        let mut verifier = Verifier::new(
            current_dir.clone(),
            config,
            Some("real.double_sum".to_string()),
        )
        .expect("Failed to create verifier");
        verifier.builder.reverify = false; // Run search like verify does
        verifier.builder.check_hashes = false; // Don't skip based on hashes

        let output = verifier.run().unwrap();
        if !output.status.is_good() {
            println!("exiting.");
            std::process::exit(1);
        }
    }
}
