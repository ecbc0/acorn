use crate::atom::AtomId;
use crate::literal::Literal;
use crate::term::{Term, TypeId};

// An ExtendedTerm is like a term in the sense that a comparison between two of them can be converted
// into a CNF formula.
// They can be Boolean or have non-Boolean types.
pub enum ExtendedTerm {
    // true = positive.
    Signed(Term, bool),

    // (condition, then branch, else branch)
    If(Literal, Term, Term),

    // Lambda(args, body) represents the value f such that f(args) = body.
    Lambda(Vec<(AtomId, TypeId)>, Term),
}

impl std::fmt::Display for ExtendedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtendedTerm::Signed(term, positive) => {
                if *positive {
                    write!(f, "{}", term)
                } else {
                    write!(f, "not {}", term)
                }
            }
            ExtendedTerm::If(condition, then_branch, else_branch) => {
                write!(
                    f,
                    "if {} then {} else {}",
                    condition, then_branch, else_branch
                )
            }
            ExtendedTerm::Lambda(args, body) => {
                write!(f, "function(")?;
                for (i, (arg_id, _)) in args.iter().enumerate() {
                    if i > 0 {
                        write!(f, ", ")?;
                    }
                    write!(f, "x{}", arg_id,)?;
                }
                write!(f, ") {{ {} }}", body)
            }
        }
    }
}

impl ExtendedTerm {
    /// Apply arguments to an ExtendedTerm, similar to Term::apply.
    /// Returns an error if trying to apply to a negative term.
    pub fn apply(&self, args: &[Term], result_type: TypeId) -> Result<ExtendedTerm, String> {
        match self {
            ExtendedTerm::Signed(term, sign) => {
                if !sign {
                    return Err("cannot apply arguments to a negative term".to_string());
                }
                Ok(ExtendedTerm::Signed(term.apply(args, result_type), true))
            }
            ExtendedTerm::If(cond, then_term, else_term) => {
                let new_then = then_term.apply(args, result_type);
                let new_else = else_term.apply(args, result_type);
                Ok(ExtendedTerm::If(cond.clone(), new_then, new_else))
            }
            ExtendedTerm::Lambda(lambda_args, body) => {
                if args.len() < lambda_args.len() {
                    // Partial application - not yet supported
                    return Err("partial application of lambda not yet supported".to_string());
                } else if args.len() == lambda_args.len() {
                    // Exact application - substitute the arguments into the body
                    let replacements: Vec<_> = lambda_args
                        .iter()
                        .zip(args.iter())
                        .map(|((var_id, _), arg)| (*var_id, arg))
                        .collect();
                    let result = body.replace_variables(&replacements);
                    Ok(ExtendedTerm::Signed(result, true))
                } else {
                    // Over-application - apply lambda args first, then apply the rest
                    let (lambda_args_slice, rest_args) = args.split_at(lambda_args.len());
                    let replacements: Vec<_> = lambda_args
                        .iter()
                        .zip(lambda_args_slice.iter())
                        .map(|((var_id, _), arg)| (*var_id, arg))
                        .collect();
                    let result = body.replace_variables(&replacements);
                    let applied = result.apply(rest_args, result_type);
                    Ok(ExtendedTerm::Signed(applied, true))
                }
            }
        }
    }
}
