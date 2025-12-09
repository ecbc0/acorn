//! Fingerprint data structure aliases that can be switched between implementations
//! using feature flags.
//!
//! - Default: uses OldFingerprintUnifier/OldFingerprintSpecializer
//! - `--features new_fingerprint`: uses NewFingerprintUnifier/NewFingerprintSpecializer
//! - `--features hybrid_fingerprint`: uses HybridFingerprintUnifier/HybridFingerprintSpecializer
//!   (runs both and panics on mismatch)

#[cfg(feature = "hybrid_fingerprint")]
pub use crate::kernel::hybrid_fingerprint::HybridFingerprintSpecializer as FingerprintSpecializer;
#[cfg(feature = "hybrid_fingerprint")]
pub use crate::kernel::hybrid_fingerprint::HybridFingerprintUnifier as FingerprintUnifier;

#[cfg(all(feature = "new_fingerprint", not(feature = "hybrid_fingerprint")))]
pub use crate::kernel::new_fingerprint::NewFingerprintSpecializer as FingerprintSpecializer;
#[cfg(all(feature = "new_fingerprint", not(feature = "hybrid_fingerprint")))]
pub use crate::kernel::new_fingerprint::NewFingerprintUnifier as FingerprintUnifier;

#[cfg(not(any(feature = "new_fingerprint", feature = "hybrid_fingerprint")))]
pub use crate::kernel::old_fingerprint::OldFingerprintSpecializer as FingerprintSpecializer;
#[cfg(not(any(feature = "new_fingerprint", feature = "hybrid_fingerprint")))]
pub use crate::kernel::old_fingerprint::OldFingerprintUnifier as FingerprintUnifier;
