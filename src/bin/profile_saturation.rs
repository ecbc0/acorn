// A representative run of the prover, to use for profiling.
//
// To profile using samply:
//
//   cargo build --bin=profile_prover --profile=fastdev
//   samply record target/fastdev/profile_prover

use acorn::{
    builder::Builder,
    project::{Project, ProjectConfig},
};
use mimalloc::MiMalloc;
use tokio_util::sync::CancellationToken;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    let current_dir = std::env::current_dir().unwrap();
    for _ in 0..10 {
        let mut project = Project::new_local(&current_dir, ProjectConfig::default()).unwrap();
        project
            .add_target_by_name("nat")
            .expect("Failed to add nat target");
        project
            .add_target_by_name("nat_gcd")
            .expect("Failed to add nat_gcd target");
        project
            .add_target_by_name("int")
            .expect("Failed to add int target");
        let mut builder = Builder::new(&project, CancellationToken::new(), |event| {
            if let Some(m) = event.log_message {
                println!("{}", m);
            }
            if let Some((d, t)) = event.progress {
                if d == t {
                    println!("{}/{} done", d, t);
                }
            }
        });
        builder.check_hashes = false;
        builder.build();
    }
}
