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

    // Test 2: Inference
    println!("\n=== Test 2: Inference ===");
    let prompt = "theorem:";
    println!("Prompt: '{}'", prompt);

    match model.infer(prompt) {
        Ok(logits) => {
            println!("Inference successful!");
            println!("Logits shape: {:?}", logits.shape());
            println!(
                "Logits range: [{:.2}, {:.2}]",
                logits.iter().copied().fold(f32::INFINITY, f32::min),
                logits.iter().copied().fold(f32::NEG_INFINITY, f32::max)
            );

            // Sample a token
            let next_token = model.sample_token(&logits, 1.0);
            let next_text = model.decode(&[next_token]);
            println!("Sampled next token: {} ('{}')", next_token, next_text);
        }
        Err(e) => {
            eprintln!("Inference error: {}", e);
            std::process::exit(1);
        }
    }

    // Test 3: Generation
    println!("\n=== Test 3: Text Generation ===");
    let gen_prompt = "define add(x: Nat, y: Nat) -> Nat {\n";
    println!("Generation prompt:\n{}", gen_prompt);

    match model.generate_simple(gen_prompt, 100, 0.8) {
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
