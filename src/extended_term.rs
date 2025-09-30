use crate::atom::AtomId;
use crate::literal::Literal;
use crate::term::{Term, TypeId};

// An ExtendedTerm is like a term in the sense that a comparison between two of them can be converted
// into a CNF formula.
// They can be Boolean or have non-Boolean types.
pub enum ExtendedTerm {
    Term(Term),

    // (condition, then branch, else branch)
    If(Literal, Term, Term),

    // Lambda(args, body) represents the value f such that f(args) = body.
    Lambda(Vec<(AtomId, TypeId)>, Term),
}

impl std::fmt::Display for ExtendedTerm {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ExtendedTerm::Term(term) => write!(f, "{}", term),
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
    pub fn apply(&self, args: &[Term], result_type: TypeId) -> Result<ExtendedTerm, String> {
        match self {
            ExtendedTerm::Term(term) => {
                Ok(ExtendedTerm::Term(term.apply(args, result_type)))
            }
            ExtendedTerm::If(cond, then_term, else_term) => {
                let new_then = then_term.apply(args, result_type);
                let new_else = else_term.apply(args, result_type);
                Ok(ExtendedTerm::If(cond.clone(), new_then, new_else))
            }
            ExtendedTerm::Lambda(lambda_args, body) => {
                if args.len() < lambda_args.len() {
                    // Partial application - substitute some args and return a new lambda
                    let (applied_args, remaining_args) = lambda_args.split_at(args.len());
                    let var_ids: Vec<_> = applied_args.iter().map(|(var_id, _)| *var_id).collect();
                    let terms: Vec<_> = args.iter().collect();
                    let new_body = body.replace_variables(&var_ids, &terms);
                    Ok(ExtendedTerm::Lambda(remaining_args.to_vec(), new_body))
                } else if args.len() == lambda_args.len() {
                    // Exact application - substitute the arguments into the body
                    let var_ids: Vec<_> = lambda_args.iter().map(|(var_id, _)| *var_id).collect();
                    let terms: Vec<_> = args.iter().collect();
                    let result = body.replace_variables(&var_ids, &terms);
                    Ok(ExtendedTerm::Term(result))
                } else {
                    // Over-application - apply lambda args first, then apply the rest
                    let (lambda_args_slice, rest_args) = args.split_at(lambda_args.len());
                    let var_ids: Vec<_> = lambda_args.iter().map(|(var_id, _)| *var_id).collect();
                    let terms: Vec<_> = lambda_args_slice.iter().collect();
                    let result = body.replace_variables(&var_ids, &terms);
                    let applied = result.apply(rest_args, result_type);
                    Ok(ExtendedTerm::Term(applied))
                }
            }
        }
    }
}
