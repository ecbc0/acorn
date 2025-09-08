// A representative run of the verifier, to use for profiling.
//
// To profile using samply:
//
//   cargo build --bin=profile_verifier --profile=fastdev
//   samply record target/fastdev/profile_verifier

use acorn::{project::ProjectConfig, verifier::Verifier};

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    for _ in 0..1 {
        let config = ProjectConfig::default();
        let verifier = Verifier::new(
            current_dir.clone(),
            config,
            Some("rat.rat_base".to_string()),
        )
        .expect("Failed to create verifier");

        match verifier.run() {
            Ok(output) => {
                println!(
                    "Verification completed: {} theorems verified",
                    output.num_verified()
                );
            }
            Err(e) => {
                println!("Verification failed: {}", e);
            }
        }
    }
}
