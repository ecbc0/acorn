use crate::kernel::aliases::Term;
use crate::kernel::atom::{Atom, AtomId};
use crate::kernel::closed_type::ClosedType;
use crate::kernel::local_context::LocalContext;
use crate::kernel::term::TermRef;
use crate::kernel::types::{GroundTypeId, TypeId, EMPTY};

// Re-export the pattern tree types from new_pattern_tree
pub use crate::new_pattern_tree::term_key_prefix;
pub use crate::new_pattern_tree::NewLiteralSet as LiteralSet;
pub use crate::new_pattern_tree::NewPatternTree as PatternTree;

/// Replaces variables in a term with corresponding replacement terms.
/// Variables x_i are replaced with replacements[i].
/// If a variable index >= replacements.len() and shift is Some, the variable is shifted.
/// If a variable index >= replacements.len() and shift is None, panics.
///
/// Also builds the output context from:
/// - The replacement_context (for variables in replacements)
/// - The term_context (for shifted variables)
pub fn replace_term_variables(
    term: &Term,
    term_context: &LocalContext,
    replacements: &[TermRef],
    replacement_context: &LocalContext,
    shift: Option<AtomId>,
) -> (Term, LocalContext) {
    let mut output_var_types: Vec<TypeId> = replacement_context.var_types.clone();
    let mut output_closed_types: Vec<ClosedType> =
        replacement_context.get_var_closed_types().to_vec();

    fn replace_recursive(
        term: TermRef,
        term_context: &LocalContext,
        replacements: &[TermRef],
        shift: Option<AtomId>,
        output_var_types: &mut Vec<TypeId>,
        output_closed_types: &mut Vec<ClosedType>,
        empty_type: ClosedType,
    ) -> Term {
        let head = term.get_head_atom();

        if let Atom::Variable(var_id) = head {
            let idx = *var_id as usize;
            if idx < replacements.len() {
                // Replace with the replacement term
                let replacement = replacements[idx];
                if term.has_args() {
                    // f(args) where f is a variable being replaced
                    // Result: replacement applied to args
                    let replacement_term = replacement.to_owned();
                    let replaced_args: Vec<Term> = term
                        .iter_args()
                        .map(|arg| {
                            replace_recursive(
                                arg,
                                term_context,
                                replacements,
                                shift,
                                output_var_types,
                                output_closed_types,
                                empty_type.clone(),
                            )
                        })
                        .collect();
                    replacement_term.apply(&replaced_args)
                } else {
                    // Just a variable, return the replacement
                    replacement.to_owned()
                }
            } else {
                // Shift the variable
                let new_var_id = match shift {
                    Some(s) => *var_id + s,
                    None => panic!("no replacement for variable x{}", var_id),
                };
                // Track the type for the shifted variable
                let new_idx = new_var_id as usize;
                let var_type_id = term_context.get_var_type(idx).unwrap_or(EMPTY);
                let var_closed_type = term_context
                    .get_var_closed_type(idx)
                    .cloned()
                    .unwrap_or_else(|| empty_type.clone());
                if new_idx >= output_closed_types.len() {
                    output_var_types.resize(new_idx + 1, EMPTY);
                    output_closed_types.resize(new_idx + 1, empty_type.clone());
                }
                output_var_types[new_idx] = var_type_id;
                output_closed_types[new_idx] = var_closed_type;

                if term.has_args() {
                    let replaced_args: Vec<Term> = term
                        .iter_args()
                        .map(|arg| {
                            replace_recursive(
                                arg,
                                term_context,
                                replacements,
                                shift,
                                output_var_types,
                                output_closed_types,
                                empty_type.clone(),
                            )
                        })
                        .collect();
                    Term::new(Atom::Variable(new_var_id), replaced_args)
                } else {
                    Term::atom(Atom::Variable(new_var_id))
                }
            }
        } else {
            // Not a variable head - recurse into args if any
            if term.has_args() {
                let replaced_args: Vec<Term> = term
                    .iter_args()
                    .map(|arg| {
                        replace_recursive(
                            arg,
                            term_context,
                            replacements,
                            shift,
                            output_var_types,
                            output_closed_types,
                            empty_type.clone(),
                        )
                    })
                    .collect();
                Term::new(*head, replaced_args)
            } else {
                term.to_owned()
            }
        }
    }

    let empty_type = ClosedType::ground(GroundTypeId::new(EMPTY.as_u16()));
    let result_term = replace_recursive(
        term.as_ref(),
        term_context,
        replacements,
        shift,
        &mut output_var_types,
        &mut output_closed_types,
        empty_type,
    );
    let result_context =
        LocalContext::from_types_and_closed_types(output_var_types, output_closed_types);
    (result_term, result_context)
}
