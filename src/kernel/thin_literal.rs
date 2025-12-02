use serde::{Deserialize, Serialize};

use crate::kernel::thin_term::ThinTerm;

/// A thin literal stores the structure of a literal without type information.
/// Like Literal, it represents an equation (or inequality) between two terms.
/// Type information is stored separately in the TypeStore and SymbolTable.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Serialize, Deserialize)]
pub struct ThinLiteral {
    pub positive: bool,
    pub left: ThinTerm,
    pub right: ThinTerm,
}

impl ThinLiteral {
    pub fn new(positive: bool, left: ThinTerm, right: ThinTerm) -> ThinLiteral {
        ThinLiteral {
            positive,
            left,
            right,
        }
    }
}
