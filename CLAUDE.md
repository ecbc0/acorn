## Instructions

- When writing Rust code, before telling the user you're finished, you should run the tests, check, and autoformat:
  `cargo test`
  `cargo check`
  `cargo fmt`

- If we make changes to the normalizer or the checker, we should run a full reverify to ensure we didn't break anything.
  `cargo run --profile release -- --reverify`

  This verifies the code in `~/acornlib`, which you can inspect to figure out verification failures.

- In no circumstances should you give up, stop, and just leave the code commented that you couldn't do what you were asked.
  If you are struggling to complete your task, ask the user for further guidance.

## Project Structure

- `/src` - Core Rust implementation
- `/vscode` - VS Code extension and assistant interface
- `/python` - Training scripts for the scoring model
