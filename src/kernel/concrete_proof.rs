use super::clause::Clause;

/// A concrete proof is an intermediate representation between the Proof (which has
/// generic clauses with variable maps) and the Certificate (which is strings).
///
/// # Design: In-Memory vs Serialized Representation
///
/// `ConcreteProof` is the **in-memory** representation with resolved numeric IDs
/// (e.g., `Symbol::GlobalConstant(123)`). This is efficient for checking but would
/// be **brittle** if serialized directly - adding a constant could shift all IDs.
///
/// The **serialized** representation (Certificate) uses names instead of IDs.
/// This makes certificates robust to refactoring: renaming, reordering definitions,
/// or adding unrelated code won't invalidate existing certificates.
///
/// The conversion flow is:
/// - **Proof generation**: `Proof` → `ConcreteProof` → `Certificate` (names)
/// - **Proof checking**: `Certificate` (names) → `ConcreteProof` (IDs) → Checker
///
/// Name resolution happens at the Certificate ↔ ConcreteProof boundary, using the
/// current codebase's bindings. This is what makes certificates survive refactoring.
///
/// # Claims vs Full Proof Structure
///
/// `ConcreteProof` stores only the **claims** to verify, not the full proof structure
/// (which rule derived each step, what it depends on, etc.). This is intentional:
/// - The checker figures out *how* to verify each claim
/// - Claims survive when their justification changes (e.g., a lemma is renamed)
/// - Only genuinely unprovable claims cause certificate failures
///
/// See also: `Certificate` for the string-based serialization format.
#[derive(Debug, Clone)]
pub struct ConcreteProof {
    /// The name of the goal that was proved.
    pub goal: String,

    /// The claims in order. Each is checked against the current state, then added.
    /// Clauses may have free variables representing universally quantified values.
    pub claims: Vec<Clause>,
}
