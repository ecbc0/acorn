// The Acorn CLI.
// You can run a language server, verify a file, or reverify the whole project.

use acorn::builder::ProverConfig;
use acorn::cleaner::{ModuleCleaner, ProjectCleaner};
use acorn::doc_generator::DocGenerator;
use acorn::generative::generative_prover::GenerativeProverConfig;
use acorn::module::ModuleDescriptor;
use acorn::project::{Project, ProjectConfig};
use acorn::server::{run_server, ServerArgs};
use acorn::verifier::Verifier;
use clap::{Parser, Subcommand};
use mimalloc::MiMalloc;
use tracing_subscriber::{fmt, prelude::*, EnvFilter};

#[global_allocator]
static GLOBAL: MiMalloc = MiMalloc;

#[derive(Parser)]
#[clap(
    name = "acorn",
    about = "A theorem prover and programming language",
    long_about = "Acorn is a theorem prover and programming language.\n\nYou can:\n- Run a language server for IDE integration\n- Verify theorems and proofs\n- Generate documentation\n- Generate training data",
    version = env!("CARGO_PKG_VERSION")
)]
struct Args {
    /// Set the directory to look for acornlib
    #[clap(
        long,
        global = true,
        help = "Set the directory to look for acornlib.",
        value_name = "DIR"
    )]
    lib: Option<String>,

    #[clap(subcommand)]
    command: Option<Command>,
}

// Note that we cannot use flags named "--update" or "--clean" because those get intercepted by the JS wrapper.
#[derive(Subcommand)]
enum Command {
    /// Run the language server for IDE integration
    Serve {
        /// The root folder the user has open
        #[clap(long)]
        workspace_root: Option<String>,

        /// The root folder of the extension
        #[clap(long)]
        extension_root: String,
    },

    /// Generate documentation
    Docs {
        /// Directory to generate documentation in
        #[clap(value_name = "DIR")]
        dir: String,
    },

    /// Generate training data
    Training {
        /// Directory to generate training data in
        #[clap(value_name = "DIR")]
        dir: String,
    },

    /// Verify theorems and proofs (default)
    Verify {
        /// Target module or file to verify (can be a filename or module name)
        #[clap(
            value_name = "TARGET",
            help = "Module or filename to verify. If not provided, verifies all files in the library. If \"-\" is provided, it reads from stdin."
        )]
        target: Option<String>,

        /// Don't skip goals based on hash checks
        #[clap(long, help = "Don't skip goals based on hash checks.")]
        nohash: bool,

        /// Search for a proof at a specific line number (requires target)
        #[clap(
            long,
            help = "Search for a proof at a specific line number.",
            value_name = "LINE"
        )]
        line: Option<u32>,

        /// Reject any use of the axiom keyword
        #[clap(
            long,
            default_value = "false",
            help = "Reject any use of the axiom keyword."
        )]
        strict: bool,
    },

    /// Reverify all goals, erroring if any goal requires a search
    Reverify {
        /// Target module or file to reverify (can be a filename or module name)
        #[clap(
            value_name = "TARGET",
            help = "Module or filename to reverify. If not provided, reverifies all files in the library."
        )]
        target: Option<String>,

        /// Search for a proof at a specific line number (requires target)
        #[clap(
            long,
            help = "Search for a proof at a specific line number.",
            value_name = "LINE"
        )]
        line: Option<u32>,

        /// Use a specific certificate instead of the cached one (requires --line)
        #[clap(
            long,
            help = "Use a specific certificate (JSON format) instead of the cached one.",
            value_name = "CERT"
        )]
        cert: Option<String>,
    },

    /// Re-prove goals without using the cache (neither reads from nor writes to cache)
    Reprove {
        /// Target module or file to reprove (can be a filename or module name)
        #[clap(
            value_name = "TARGET",
            help = "Module or filename to reprove. If not provided, reproves all files in the library."
        )]
        target: Option<String>,

        /// Search for a proof at a specific line number (requires target)
        #[clap(
            long,
            help = "Search for a proof at a specific line number.",
            value_name = "LINE"
        )]
        line: Option<u32>,

        /// Use the generative prover instead of the saturation prover
        #[clap(
            long,
            help = "Path to the directory containing the generative model (model.onnx, tokenizer.json, config.json)",
            value_name = "MODEL_DIR"
        )]
        generative: Option<String>,

        /// Exit immediately on the first verification failure
        #[clap(long, help = "Exit immediately on the first verification failure.")]
        fail_fast: bool,
    },

    /// Display proof details for a specific line
    Select {
        /// Module or file to select from
        #[clap(value_name = "MODULE")]
        module: String,

        /// Line number to select
        #[clap(value_name = "LINE")]
        line: u32,
    },

    /// Remove redundant claims from a module or entire project
    Clean {
        /// Module name to clean (if not provided, cleans all modules in the project)
        #[clap(value_name = "MODULE")]
        module: Option<String>,
    },
}

#[tokio::main]
async fn main() {
    // Initialize tracing subscriber with env filter
    // Use RUST_LOG env var to control log levels, e.g.:
    //   RUST_LOG=acorn::processor=debug cargo run -- verify
    //   RUST_LOG=acorn::processor=trace cargo run -- verify
    tracing_subscriber::registry()
        .with(fmt::layer().with_ansi(false).without_time())
        .with(EnvFilter::try_from_default_env().unwrap_or_else(|_| EnvFilter::new("warn")))
        .init();

    let args = Args::parse();

    let current_dir = if let Some(lib_dir) = &args.lib {
        std::path::PathBuf::from(lib_dir)
    } else {
        match std::env::current_dir() {
            Ok(dir) => dir,
            Err(e) => {
                println!("Error getting current directory: {}", e);
                std::process::exit(1);
            }
        }
    };

    match args.command {
        Some(Command::Serve {
            workspace_root,
            extension_root,
        }) => {
            let server_args = ServerArgs {
                workspace_root,
                extension_root,
            };
            run_server(&server_args).await;
        }

        Some(Command::Docs { dir }) => {
            let mut project = Project::new_local(&current_dir, ProjectConfig::default())
                .unwrap_or_else(|e| {
                    println!("Error loading project: {}", e);
                    std::process::exit(1);
                });
            project.add_src_targets();
            match DocGenerator::new(&project).generate(&dir) {
                Ok(count) => {
                    println!("{} files generated in {}", count, dir);
                }
                Err(e) => {
                    println!("Error generating documentation: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Some(Command::Training { dir }) => {
            let mut verifier = match Verifier::new(current_dir, ProjectConfig::default(), None) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            // Training mode automatically enables reverify and disables hash checking
            verifier.builder.reverify = true;
            verifier.builder.check_hashes = false;
            if let Err(e) = verifier.builder.set_training_output_dir(&dir) {
                println!("Error setting training output directory: {}", e);
                std::process::exit(1);
            }

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }

        Some(Command::Verify {
            target,
            nohash,
            line,
            strict,
        }) => {
            let mut verifier = match Verifier::new(current_dir, ProjectConfig::default(), target) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.verbose = line.is_some();
            verifier.line = line;
            verifier.builder.reverify = false;
            verifier.builder.strict = strict;
            verifier.builder.check_hashes = !nohash && !strict;

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }

        Some(Command::Reverify { target, line, cert }) => {
            // Validate that cert requires line
            if cert.is_some() && line.is_none() {
                println!("Error: --cert requires --line to be set");
                std::process::exit(1);
            }

            let mut verifier = match Verifier::new(current_dir, ProjectConfig::default(), target) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.verbose = line.is_some();
            verifier.line = line;
            verifier.builder.reverify = true;
            verifier.builder.check_hashes = false;
            verifier.builder.operation_verb = "reverified";

            // Parse and set the certificate override if provided
            if let Some(cert_json) = cert {
                match serde_json::from_str::<acorn::certificate::Certificate>(&cert_json) {
                    Ok(certificate) => {
                        verifier.builder.cert_override = Some(certificate);
                    }
                    Err(e) => {
                        println!("Error parsing certificate JSON: {}", e);
                        std::process::exit(1);
                    }
                }
            }

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }

        Some(Command::Reprove {
            target,
            line,
            generative,
            fail_fast,
        }) => {
            // Create a config that disables both reading and writing to the cache
            let config = ProjectConfig {
                use_filesystem: true,
                read_cache: false,
                write_cache: false,
            };

            // Create the prover config based on the --generative flag
            let prover_config = if let Some(model_path) = generative {
                let mut gen_config = GenerativeProverConfig::default();
                gen_config.generative_model_path = model_path;
                ProverConfig::Generative(gen_config)
            } else {
                ProverConfig::default()
            };

            let mut verifier =
                match Verifier::with_prover(current_dir, config, target, prover_config) {
                    Ok(v) => v,
                    Err(e) => {
                        println!("{}", e);
                        std::process::exit(1);
                    }
                };

            verifier.builder.verbose = line.is_some();
            verifier.line = line;
            verifier.builder.reverify = false; // Run search like verify does
            verifier.builder.check_hashes = false; // Don't skip based on hashes
            verifier.builder.operation_verb = "reproved";
            verifier.exit_on_warning = fail_fast;

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }

        Some(Command::Select { module, line }) => {
            let mut project = Project::new_local(&current_dir, ProjectConfig::default())
                .unwrap_or_else(|e| {
                    println!("Error loading project: {}", e);
                    std::process::exit(1);
                });

            // Add target and resolve path, same way as verify does
            let path = if module.ends_with(".ac") {
                // Treat as a filename
                let path = std::path::PathBuf::from(&module);
                if let Err(e) = project.add_target_by_path(&path) {
                    println!("Error loading module: {}", e);
                    std::process::exit(1);
                }
                path
            } else {
                // Treat as a module name
                if let Err(e) = project.add_target_by_name(&module) {
                    println!("Error loading module '{}': {}", module, e);
                    std::process::exit(1);
                }
                match project.path_from_module_name(&module) {
                    Ok(path) => path,
                    Err(e) => {
                        println!("Error resolving module '{}': {}", module, e);
                        std::process::exit(1);
                    }
                }
            };

            match project.handle_selection(&path, line - 1) {
                Ok((goal_infos, _range)) => {
                    if goal_infos.is_empty() {
                        println!("No goals found at this location.");
                    } else {
                        for (i, goal_info) in goal_infos.iter().enumerate() {
                            if goal_infos.len() > 1 {
                                println!("Goal {}: {}", i + 1, goal_info.goal_name);
                            } else {
                                println!("{}", goal_info.goal_name);
                            }
                            println!();

                            if let Some(ref steps) = goal_info.steps {
                                if steps.is_empty() {
                                    println!("Trivial.");
                                } else {
                                    let step_word = if steps.len() == 1 { "step" } else { "steps" };
                                    println!(
                                        "The detailed proof has {} {}:\n",
                                        steps.len(),
                                        step_word
                                    );

                                    // Find the maximum width for statement column
                                    let max_statement_width = steps
                                        .iter()
                                        .map(|s| s.statement.len())
                                        .max()
                                        .unwrap_or(20)
                                        .max(20); // Minimum width of 20

                                    // Print header
                                    println!(
                                        "{:<width$}    Reason",
                                        "Statement",
                                        width = max_statement_width
                                    );

                                    // Print each step
                                    for step in steps {
                                        println!(
                                            "{:<width$}    {}",
                                            step.statement,
                                            step.reason,
                                            width = max_statement_width
                                        );
                                    }
                                }
                            } else {
                                println!("No proof available.");
                            }

                            if i < goal_infos.len() - 1 {
                                println!();
                                println!("---");
                                println!();
                            }
                        }
                    }
                }
                Err(e) => {
                    println!("Error: {}", e);
                    std::process::exit(1);
                }
            }
        }

        Some(Command::Clean { module }) => {
            match module {
                Some(module_name) => {
                    // Clean a specific module
                    let module_spec = ModuleDescriptor::name(&module_name);
                    let cleaner = ModuleCleaner::new(current_dir, module_spec);

                    match cleaner.clean() {
                        Ok(_stats) => {
                            // Stats are already printed by clean()
                        }
                        Err(e) => {
                            println!("Error cleaning module: {:?}", e);
                            std::process::exit(1);
                        }
                    }
                }
                None => {
                    // Clean the entire project
                    let cleaner = ProjectCleaner::new(current_dir);

                    match cleaner.clean() {
                        Ok(_stats) => {
                            // Stats are already printed by clean()
                        }
                        Err(e) => {
                            println!("Error cleaning project: {:?}", e);
                            std::process::exit(1);
                        }
                    }
                }
            }
        }

        // Default to do a global verify if no subcommand is provided
        None => {
            let mut verifier = match Verifier::new(current_dir, ProjectConfig::default(), None) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.reverify = false;
            verifier.builder.check_hashes = true;

            match verifier.run() {
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
                Ok(output) => {
                    if !output.is_success() {
                        std::process::exit(1);
                    }
                }
            }
        }
    }
}
