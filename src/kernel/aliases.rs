//! Type aliases that switch between Fat and Thin implementations based on feature flags.

#[cfg(not(feature = "thin"))]
pub use crate::kernel::fat_clause::FatClause as Clause;
#[cfg(not(feature = "thin"))]
pub use crate::kernel::fat_literal::FatLiteral as Literal;
#[cfg(not(feature = "thin"))]
pub use crate::kernel::fat_term::FatTerm as Term;

#[cfg(feature = "thin")]
pub use crate::kernel::thin_clause::ThinClause as Clause;
#[cfg(feature = "thin")]
pub use crate::kernel::thin_literal::ThinLiteral as Literal;
#[cfg(feature = "thin")]
pub use crate::kernel::thin_term::ThinTerm as Term;
