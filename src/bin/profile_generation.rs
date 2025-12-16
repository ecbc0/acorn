// A performance profiler for the generative prover.
//
// Usage:
//   cargo build --bin=profile_generation --profile=release
//   ./target/release/profile_generation <model_path>
//
// For profiling with samply:
//   samply record target/release/profile_generation <model_path>

use std::env;
use std::path::PathBuf;
use std::time::Instant;

use acorn::checker::Checker;
use acorn::generative::generative_prover::{GenerativeProver, GenerativeProverConfig};
use acorn::generative::goal_context::GoalContext;
use acorn::normalizer::Normalizer;
use acorn::project::{Project, ProjectConfig};

use mimalloc::MiMalloc;

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

fn main() {
    // Parse command line arguments
    let args: Vec<String> = env::args().collect();
    if args.len() != 2 {
        eprintln!("Usage: {} <model_path>", args[0]);
        eprintln!();
        eprintln!("Example:");
        eprintln!("  {} ~/models/generative_model", args[0]);
        std::process::exit(1);
    }

    let model_path = &args[1];
    println!("Loading generative model from: {}", model_path);

    // Create the config
    let config = GenerativeProverConfig {
        generative_model_path: model_path.to_string(),
        num_steps_per_rollout: 100, // 100 steps per rollout
        max_tokens_per_line: 100,
        temperature: 0.8,
        time_limit_secs: 5.0, // 5 second time limit
    };

    // Load the project (using acornlib)
    println!("Loading project...");
    let acornlib_path = PathBuf::from(env::var("HOME").unwrap()).join("acornlib");
    let mut project = Project::new_local(&acornlib_path, ProjectConfig::default())
        .expect("Failed to load project");

    // Add a target with some goals to test on
    println!("Loading module: complex...");
    let module_id = project
        .load_module_by_name("complex")
        .expect("complex module not found");
    let env = project
        .get_env_by_id(module_id)
        .expect("No env for complex module");

    let goal_cursor = env
        .iter_goals()
        .next()
        .expect("No goals found in complex module");

    let goal = goal_cursor.goal().expect("Failed to get goal from cursor");

    println!("Found goal: {} (module: {})", goal.name, module_id);

    // Create a GoalContext from the goal
    let goal_context =
        GoalContext::from_project_and_goal(&project, &goal).expect("Failed to create goal context");

    println!("Goal context created");
    println!();

    // Initialize the generative prover
    println!("Initializing generative prover...");
    let mut prover = GenerativeProver::new(config.clone());

    // Create a checker
    let checker = Checker::new();

    // Set the goal context (initializes the KV cache)
    println!("Setting goal context and warming up KV cache...");
    let cache_start = Instant::now();
    prover
        .set_goal_context(goal_context)
        .expect("Failed to set goal context");
    let cache_duration = cache_start.elapsed();
    println!(
        "KV cache initialized in {:.2}ms",
        cache_duration.as_secs_f64() * 1000.0
    );
    println!();

    // Prepare bindings and normalizer
    let bindings = &env.bindings;
    let normalizer = Normalizer::new();

    // Run generation performance test
    println!("Starting generation performance test...");
    println!("Configuration:");
    println!("  - Max tokens per line: {}", config.max_tokens_per_line);
    println!("  - Temperature: {}", config.temperature);
    println!(
        "  - Max steps per rollout: {}",
        config.num_steps_per_rollout
    );
    println!("  - Time limit: {:.1}s", config.time_limit_secs);
    println!();

    let overall_start = Instant::now();

    // Run the search (multiple rollouts until time limit)
    let outcome = prover.search(&project, bindings, &normalizer, &checker);

    let overall_duration = overall_start.elapsed();

    // Get statistics from the prover
    let (total_successful_lines, total_failed_attempts) = prover.stats();
    let total_tokens_generated = (total_successful_lines + total_failed_attempts) * 50; // Estimate

    // Print statistics
    println!();
    println!("=== Performance Results ===");
    println!("Outcome: {:?}", outcome);
    println!("Total duration: {:.2}s", overall_duration.as_secs_f64());
    println!("Successful lines: {}", total_successful_lines);
    println!("Failed attempts: {}", total_failed_attempts);
    println!(
        "Success rate: {:.1}%",
        if total_successful_lines + total_failed_attempts > 0 {
            100.0 * total_successful_lines as f64
                / (total_successful_lines + total_failed_attempts) as f64
        } else {
            0.0
        }
    );
    println!();
    println!(
        "Throughput (estimated tokens): ~{} tokens",
        total_tokens_generated
    );
    println!(
        "Tokens per second: {:.1}",
        total_tokens_generated as f64 / overall_duration.as_secs_f64()
    );
    println!(
        "Lines per second: {:.2}",
        (total_successful_lines + total_failed_attempts) as f64 / overall_duration.as_secs_f64()
    );
    println!(
        "Average time per attempt: {:.2}ms",
        overall_duration.as_secs_f64() * 1000.0
            / (total_successful_lines + total_failed_attempts) as f64
    );
}
