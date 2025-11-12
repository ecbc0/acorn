// Test binary for the TacticsModel generative model.
// Usage: cargo run --bin test_gen -- <path_to_model_directory>

use acorn::generative::tactics_model::TacticsModel;
use std::env;

fn main() {
    let args: Vec<String> = env::args().collect();

    if args.len() < 2 {
        eprintln!("Usage: {} <model_directory>", args[0]);
        eprintln!(
            "Example: {} ~/tactics/export/tactics-2025-11-10-11-58-39",
            args[0]
        );
        eprintln!("\nThe directory should contain: model.onnx, tokenizer.json, and config.json");
        std::process::exit(1);
    }

    let model_path = &args[1];

    println!("Loading model from: {}", model_path);
    let model = match TacticsModel::load(model_path) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("Error loading model: {}", e);
            std::process::exit(1);
        }
    };

    println!("Model loaded successfully!");
    println!("Vocabulary size: {}", model.vocab_size());
    println!("Context length: {}", model.context_length());

    // Test 1: Encoding/decoding
    println!("\n=== Test 1: Encoding/Decoding ===");
    let test_string = "Hello, world!";
    let tokens = model.encode(test_string);
    println!("Original: {}", test_string);
    println!("Tokens: {:?}", &tokens[..tokens.len().min(20)]);
    let decoded = model.decode(&tokens);
    println!("Decoded: {}", decoded);
    assert_eq!(test_string, decoded);

    // Test 2: Inference (skipped - old infer() method doesn't work with KV cache model)
    // The generation tests below use the new KV-cached inference

    // Test 3: Generation
    println!("\n=== Test 3: Text Generation ===");
    let gen_prompt = "define add(x: Nat, y: Nat) -> Nat {\n";
    println!("Generation prompt:\n{}", gen_prompt);

    match model.generate_line(gen_prompt, 100, 0.8) {
        Ok(generated) => {
            println!("\nGenerated text ({} chars):", generated.len());
            println!("---");
            println!("{}", generated);
            println!("---");
        }
        Err(e) => {
            eprintln!("Generation error: {}", e);
            std::process::exit(1);
        }
    }

    println!("\n=== All tests passed! ===");
}
