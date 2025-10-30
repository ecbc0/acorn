use std::error::Error;
use std::sync::OnceLock;

use ort::execution_providers::CPUExecutionProvider;

// Global flag to ensure ORT is initialized only once
static ORT_INITIALIZED: OnceLock<()> = OnceLock::new();

/// Ensures that ONNX Runtime is initialized exactly once.
/// This should be called before creating any ORT sessions.
/// Multiple calls are safe - only the first call will perform initialization.
pub fn ensure_ort_initialized() -> Result<(), Box<dyn Error>> {
    ORT_INITIALIZED.get_or_init(|| {
        ort::init()
            .with_execution_providers([CPUExecutionProvider::default().build().error_on_failure()])
            .commit()
            .expect("Failed to initialize ORT");
    });
    Ok(())
}
