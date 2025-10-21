// The Acorn CLI.
// You can run a language server, verify a file, or reverify the whole project.

use acorn::doc_generator::DocGenerator;
use acorn::project::{Project, ProjectConfig};
use acorn::server::{run_server, ServerArgs};
use acorn::verifier::Verifier;
use clap::{Parser, Subcommand};
use mimalloc::MiMalloc;

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
    },

    /// Reverify all goals, erroring if any goal requires a search
    Reverify,
}

#[tokio::main]
async fn main() {
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
            verifier.builder.check_hashes = !nohash;

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

        Some(Command::Reverify) => {
            let mut verifier = match Verifier::new(current_dir, ProjectConfig::default(), None) {
                Ok(v) => v,
                Err(e) => {
                    println!("{}", e);
                    std::process::exit(1);
                }
            };

            verifier.builder.reverify = true;
            verifier.builder.check_hashes = false;

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
