use std::cell::RefCell;
use std::path::PathBuf;
use std::rc::Rc;
use std::sync::Arc;

use crate::builder::{BuildEvent, BuildMetrics, BuildStatus, Builder};
use crate::project::{Project, ProjectConfig};

/// Output from running the verifier
#[derive(Debug)]
pub struct VerifierOutput {
    /// The overall build status
    pub status: BuildStatus,

    /// Build metrics collected during verification
    pub metrics: BuildMetrics,

    /// All build events collected during verification
    pub events: Vec<BuildEvent>,
}

impl VerifierOutput {
    /// How many verification events were collected.
    pub fn num_verified(&self) -> usize {
        self.events.iter().filter(|e| e.verified.is_some()).count()
    }

    pub fn is_success(&self) -> bool {
        self.status == BuildStatus::Good
    }
}

/// The Verifier manages the run of a single build.
pub struct Verifier {
    /// Configuration for the project
    config: ProjectConfig,

    /// The target module to verify.
    /// If None, all modules are verified.
    target: Option<String>,

    /// The starting path to find the acorn library from.
    start_path: PathBuf,

    /// Optional external line number (1-based) to verify a single goal.
    /// If this is set, target must be as well.
    pub line: Option<u32>,

    /// The verbose flag makes us print miscellaneous debug output.
    /// Don't set it from within the language server.
    pub verbose: bool,
}

impl Verifier {
    pub fn new(start_path: PathBuf, config: ProjectConfig, target: Option<String>) -> Self {
        Self {
            config,
            target,
            start_path,
            line: None,
            verbose: false,
        }
    }

    /// Returns VerifierOutput on success, or an error string if verification fails.
    pub fn run(&self) -> Result<VerifierOutput, String> {
        let mut project = match Project::new_local(&self.start_path, self.config.clone()) {
            Ok(p) => p,
            Err(e) => return Err(format!("Error: {}", e)),
        };

        if let Some(target) = &self.target {
            if target == "-" {
                let path = PathBuf::from("<stdin>");
                if let Err(e) = project.add_target_by_path(&path) {
                    return Err(format!("{}", e));
                }
            } else if target.starts_with("-:") {
                let path = PathBuf::from(target);
                if let Err(e) = project.add_target_by_path(&path) {
                    return Err(format!("{}", e));
                }
            } else if target.ends_with(".ac") {
                // Looks like a filename
                let path = PathBuf::from(&target);
                if let Err(e) = project.add_target_by_path(&path) {
                    return Err(format!("{}", e));
                }
            } else if let Err(e) = project.add_target_by_name(&target) {
                return Err(format!("{}", e));
            }
        } else {
            project.add_all_targets();
        }

        // Create a vector to collect events
        let events = Rc::new(RefCell::new(Vec::new()));
        let events_clone = events.clone();

        // Create an Arc to share the project with the closure
        let project_arc = Arc::new(project);
        let project_for_closure = Arc::clone(&project_arc);

        // Set up the builder
        let mut builder = Builder::new(Arc::as_ref(&project_arc), move |event| {
            // Also print log messages as before
            if let Some(m) = &event.log_message {
                if let Some(diagnostic) = &event.diagnostic {
                    // Use display_path to show a relative path
                    let display_path = project_for_closure.display_path(&event.module);
                    println!(
                        "{}, line {}: {}",
                        display_path,
                        diagnostic.range.start.line + 1,
                        m
                    );
                } else {
                    println!("{}", m);
                }
            }

            // Store the event
            events_clone.borrow_mut().push(event);
        });

        // Get a reference back to use in the rest of the method
        let project = Arc::as_ref(&project_arc);

        if !self.config.check_hashes {
            builder.log_when_slow = true;
        }
        if self.target.is_none() {
            builder.log_secondary_errors = false;
        }

        // If a specific line is provided along with a target, set up single goal verification
        if let Some(line) = self.line {
            let Some(target) = &self.target else {
                panic!("line set without target");
            };
            // line is the external line number (1-based)
            if let Err(e) = builder.set_single_goal(target, line, project) {
                return Err(format!("Failed to set single goal: {}", e));
            }
        }

        builder.verbose = self.verbose;

        // Build
        builder.build(&project);
        builder.metrics.print(builder.status);

        if !self.config.check_hashes && builder.metrics.searches_fallback > 0 {
            println!("Warning: the filtered prover was not able to handle all goals.");
        }

        // Create the output
        let output = VerifierOutput {
            status: builder.status,
            metrics: builder.metrics,
            events: events.take(),
        };

        Ok(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use assert_fs::fixture::ChildPath;
    use assert_fs::prelude::*;
    use assert_fs::TempDir;

    /// Creates a standard Acorn project layout with acorn.toml, src/, and build/ directories.
    /// Returns (project dir, src_dir, build_dir) for use in tests.
    /// Close the project directory after use to clean up.
    fn setup() -> (TempDir, ChildPath, ChildPath) {
        let temp = TempDir::new().unwrap();
        temp.child("acorn.toml").write_str("").unwrap();
        let src = temp.child("src");
        src.create_dir_all().unwrap();
        let build = temp.child("build");
        build.create_dir_all().unwrap();
        (temp, src, build)
    }

    #[test]
    fn test_verifier_basic() {
        let (acornlib, src, build) = setup();

        // Create foo.ac inside the src directory
        let foo_ac = src.child("foo.ac");
        foo_ac
            .write_str(
                r#"
                theorem simple_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier starting from the acornlib directory
        // The verifier should find the src directory and use it as the root
        let config = ProjectConfig {
            check_hashes: false,
            use_certs: true,
            ..Default::default()
        };
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            config,
            Some("foo".to_string()),
        );

        // Test that the verifier can run successfully on our theorem in the src directory
        let result = verifier.run();
        assert!(
            result.is_ok(),
            "Verifier should successfully verify the theorem in src directory: {:?}",
            result
        );

        // Check that we proved one goal, via search
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1);
        assert_eq!(output.metrics.goals_success, 1);
        assert_eq!(output.metrics.cached_certs, 0);
        assert_eq!(output.metrics.unused_certs, 0);
        assert_eq!(output.metrics.searches_total, 1);

        // Check that we created a file in the build directory
        let build_file = build.child("foo.yaml");
        assert!(
            build_file.exists(),
            "Module cache file should exist at build/foo.yaml"
        );

        // Check that the cert file has one line
        let cert_file = build.child("foo.jsonl");
        assert!(cert_file.exists(), "build/foo.jsonl should exist");
        let jsonl_content = std::fs::read_to_string(cert_file.path()).unwrap();
        let line_count = jsonl_content.lines().count();
        assert_eq!(line_count, 1,);

        // Verify again
        let result2 = verifier.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        // Check that we proved one goal, via cached cert
        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);
        assert_eq!(output2.metrics.goals_total, 1);
        assert_eq!(output2.metrics.goals_success, 1);
        assert_eq!(output2.metrics.cached_certs, 1);
        assert_eq!(output2.metrics.unused_certs, 0);
        assert_eq!(output2.metrics.searches_total, 0);

        // Check that the cert file still has one line
        assert!(cert_file.exists(), "build/foo.jsonl should exist");
        let jsonl_content = std::fs::read_to_string(cert_file.path()).unwrap();
        let line_count = jsonl_content.lines().count();
        assert_eq!(line_count, 1,);

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_uses_nested_cache() {
        let (acornlib, src, build) = setup();

        // Create a nested directory structure
        let foo_dir = src.child("foo");
        foo_dir.create_dir_all().unwrap();

        // Create a file at foo/bar.ac with one theorem
        let bar_ac = foo_dir.child("bar.ac");
        bar_ac
            .write_str(
                r#"
                theorem nested_truth {
                    true
                }
                "#,
            )
            .unwrap();

        // Create a verifier targeting the nested module
        let config = ProjectConfig {
            check_hashes: false,
            use_certs: true,
            ..Default::default()
        };
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            config,
            Some("foo.bar".to_string()),
        );

        // Run the verifier the first time
        let result = verifier.run();
        assert!(
            result.is_ok(),
            "First verifier run should succeed: {:?}",
            result
        );

        // Check that we actually proved something
        let output = result.unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.goals_total, 1); // Should have 1 theorem to prove
        assert_eq!(output.metrics.goals_success, 1); // Should have successfully proven 1 theorem
        assert!(output.metrics.searches_total > 0); // Should have performed at least one search

        // Check that we created a file in the nested build directory
        let build_foo_dir = build.child("foo");
        let build_file = build_foo_dir.child("bar.yaml");
        assert!(
            build_file.exists(),
            "Cache file should exist at build/foo/bar.yaml"
        );

        // Check that we created a JSONL file for certificates in the nested directory
        let cert_file = build_foo_dir.child("bar.jsonl");
        assert!(
            cert_file.exists(),
            "Certificate file should exist at build/foo/bar.jsonl"
        );

        // Verify again
        let result2 = verifier.run();
        assert!(
            result2.is_ok(),
            "Second verifier should successfully run: {:?}",
            result2
        );

        let output2 = result2.unwrap();
        assert_eq!(output2.status, BuildStatus::Good);

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_filter_picks_up_imported_extends() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property<B: Bar> {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }
        "#,
            )
            .unwrap();

        src.child("main.ac")
            .write_str(
                r#"
            from foo import Baz

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property<B: Baz> {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let config = ProjectConfig {
            check_hashes: false,
            use_certs: true,
            ..Default::default()
        };
        let verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            Some("main".to_string()),
        );
        let output = verifier1.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);

        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            config,
            Some("main".to_string()),
        );
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
        assert_eq!(output.metrics.searches_fallback, 0);

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_filter_picks_up_local_extends() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
            typeclass F: Foo {
                foo_property: Bool
            }

            typeclass B: Bar extends Foo {
                bar_property: Bool
            }

            axiom bar_has_foo_property<B: Bar> {
                B.foo_property
            }

            typeclass Baz extends Bar {
                baz_property: Bool
            }

            // To prove this, we need to know that Baz extends Bar.
            theorem baz_has_foo_property<B: Baz> {
                B.foo_property
            }
        "#,
            )
            .unwrap();

        let config = ProjectConfig {
            check_hashes: false,
            use_certs: true,
            ..Default::default()
        };
        let verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            config.clone(),
            Some("main".to_string()),
        );
        let output = verifier1.run().unwrap();
        assert_eq!(output.num_verified(), 5);

        let verifier2 = Verifier::new(
            acornlib.path().to_path_buf(),
            config,
            Some("main".to_string()),
        );
        let output = verifier2.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good,);
        assert_eq!(output.metrics.searches_fallback, 0,);
        assert_eq!(output.num_verified(), 5);

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_fails_on_circular_import() {
        let (acornlib, src, _) = setup();

        src.child("foo.ac").write_str("import bar").unwrap();
        src.child("bar.ac").write_str("import foo").unwrap();

        let config = ProjectConfig {
            check_hashes: false,
            use_certs: true,
            ..Default::default()
        };
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            config,
            Some("foo".to_string()),
        );

        let result = verifier.run();
        let Err(err) = result else {
            panic!("Verifier should fail on circular import: {:?}", result);
        };

        assert!(
            err.contains("circular"),
            "Expected circular import error, got: {}",
            err
        );

        if err.lines().map(|l| l.contains("^^^^^")).count() != 1 {
            panic!(
                "Expected exactly one ^^^^^^ line in the error message, got:\n{}",
                err
            );
        }

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_fails_on_ambiguous_import() {
        let (acornlib, src, _) = setup();

        // Create both foo.ac and foo/default.ac
        src.child("foo.ac").write_str("type Foo: axiom").unwrap();
        std::fs::create_dir_all(src.child("foo").path()).unwrap();
        src.child("foo")
            .child("default.ac")
            .write_str("type Bar: axiom")
            .unwrap();

        // Try to import the ambiguous module
        src.child("main.ac").write_str("import foo").unwrap();

        let config = ProjectConfig {
            check_hashes: false,
            use_certs: true,
            ..Default::default()
        };
        let verifier = Verifier::new(
            acornlib.path().to_path_buf(),
            config,
            Some("main".to_string()),
        );

        let result = verifier.run();
        let Ok(output) = result else {
            panic!(
                "Verifier should run but report compilation error: {:?}",
                result
            );
        };

        // The verifier should report a compilation error
        assert_eq!(output.status, BuildStatus::Error);

        // Check that the error message contains "ambiguous"
        let error_messages: Vec<String> = output
            .events
            .iter()
            .filter_map(|e| e.log_message.as_ref())
            .cloned()
            .collect();
        let error_text = error_messages.join("\n");
        assert!(
            error_text.contains("ambiguous"),
            "Expected ambiguous import error, got: {}",
            error_text
        );

        acornlib.close().unwrap();
    }

    #[test]
    fn test_verifier_concrete_local_constants() {
        let (acornlib, src, _) = setup();

        src.child("main.ac")
            .write_str(
                r#"
        inductive Nat {
            0
            suc(Nat)
        }
        attributes Nat {
            define add(self, other: Nat) -> Nat {
                match other {
                    Nat.0 {
                        self
                    }
                    Nat.suc(pred) {
                        self.add(pred).suc
                    }
                }
            }
        }

        numerals Nat

        theorem goal(a: Nat) {
            a + 0 = a
        }
        "#,
            )
            .unwrap();

        let config = ProjectConfig {
            check_hashes: false,
            use_certs: true,
            ..Default::default()
        };
        let verifier1 = Verifier::new(
            acornlib.path().to_path_buf(),
            config,
            Some("main".to_string()),
        );
        let output = verifier1.run().unwrap();
        assert_eq!(output.status, BuildStatus::Good);
    }
}
