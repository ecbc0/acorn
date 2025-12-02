use serde::{Deserialize, Serialize};

use crate::kernel::context::Context;
use crate::kernel::thin_literal::ThinLiteral;

/// A thin clause stores the structure of a clause without type information.
/// Like Clause, it represents a disjunction (an "or") of literals.
/// Type information is stored separately in the TypeStore and SymbolTable,
/// along with a Context that tracks the types of variables in the clause.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinClause {
    pub literals: Vec<ThinLiteral>,
    pub context: Context,
}

impl ThinClause {
    pub fn new(literals: Vec<ThinLiteral>, context: Context) -> ThinClause {
        ThinClause { literals, context }
    }
}
