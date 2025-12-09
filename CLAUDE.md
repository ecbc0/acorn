## Instructions

- When writing Rust code, before telling the user you're finished, you should run the tests, check, and autoformat:
  `cargo test`
  `cargo check`
  `cargo fmt`

- If we make changes to the normalizer or the kernel, we should run a full reverify to ensure we didn't
  break anything.
  `cargo run --profile release -- reverify`

  This verifies the code in `~/acornlib`, which you can inspect to figure out verification failures.

- To evaluate performance, we should do a release build:

  `cargo build --profile release`

  and then see how long it takes to run the commands:

  `time cargo run --profile release -- reverify`
  `time cargo run --profile release -- reprove real.double_sum`

  This is important to do if we are doing something performance-sensitive, like altering the basic Term
  structure, or changing how one of the key TermGraph / PatternTree / FingerprintX data structures work.

- A "full reprove" is slow, but sometimes finds obscure bugs that nothing else finds. We generally
  only want to do this when the user asks for it:

  `cargo run --profile release -- reprove`

  When you do a full reprove, it's okay if some propositions can't be verified. What indicates a real problem is if the prover crashes.

## Project Structure

- `/src` - Core Rust implementation
- `/vscode` - VS Code extension and assistant interface
- `/python` - Training scripts for the scoring model
