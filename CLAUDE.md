## Instructions

- When writing Rust code, before telling the user you're finished, you should run the tests, check, and autoformat:
  `cargo test`
  `cargo check`
  `cargo fmt`

- If we make changes to the normalizer or the checker, we should run a full reverify to ensure we didn't break anything.
  `cargo run --profile release -- --reverify`

## Project Structure

- `/src` - Core Rust implementation
- `/tests` - Test files (environment_test.rs, prover_test.rs)
- `/vscode` - VS Code extension and assistant interface
- `/python` - Training scripts for the model
