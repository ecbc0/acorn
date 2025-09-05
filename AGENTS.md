# Acorn Development Guide

This file is for LLM CLI coding tools.

## Build/Test Commands

- The Rust test suite: `cargo test -q`
- Run a single Rust test: `cargo test -q test_name`

- The slow and extensive global reverify:
  `cargo run --release -- --nohash`
  This generally doesn't have to be run, but if the user asks for it we can.

## Code Style Guidelines

- Use Rust 2021 edition idioms
- Variable names: snake_case
- Type names: PascalCase
- When adding new features, follow existing patterns for similar constructs
- For language features, make sure to test both valid and invalid inputs

## Project Structure

- `/src` - Core Rust implementation
- `/tests` - Test files (environment_test.rs, prover_test.rs)
- `/vscode` - VS Code extension and assistant interface
- `/python` - Training scripts for the model
