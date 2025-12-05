//! Type aliases that switch between Fat and Thin implementations based on feature flags.
//! By default, we use the Thin implementations for better performance.
//! Enable the "fat" feature to use Fat implementations (which embed type information in terms).

#[cfg(feature = "fat")]
pub use crate::kernel::fat_clause::FatClause as Clause;
#[cfg(feature = "fat")]
pub use crate::kernel::fat_literal::FatLiteral as Literal;
#[cfg(feature = "fat")]
pub use crate::kernel::fat_term::FatTerm as Term;

#[cfg(not(feature = "fat"))]
pub use crate::kernel::thin_clause::ThinClause as Clause;
#[cfg(not(feature = "fat"))]
pub use crate::kernel::thin_literal::ThinLiteral as Literal;
#[cfg(not(feature = "fat"))]
pub use crate::kernel::thin_term::ThinTerm as Term;
