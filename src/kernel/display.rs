use std::fmt;

use crate::kernel::aliases::{Clause, Literal, Term};
use crate::kernel::atom::Atom;
use crate::kernel::kernel_context::KernelContext;
use crate::kernel::term::TermRef;

struct DisplayAtom<'a> {
    atom: Atom,
    context: &'a KernelContext,
}

impl fmt::Display for DisplayAtom<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.context.atom_str(&self.atom))
    }
}

pub struct DisplayTerm<'a> {
    pub term: TermRef<'a>,
    pub context: &'a KernelContext,
}

impl DisplayTerm<'_> {
    pub fn from_term<'a>(term: &'a Term, context: &'a KernelContext) -> DisplayTerm<'a> {
        DisplayTerm {
            term: term.as_ref(),
            context,
        }
    }
}

impl fmt::Display for DisplayTerm<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{}",
            DisplayAtom {
                atom: *self.term.get_head_atom(),
                context: self.context
            }
        )?;
        if self.term.has_args() {
            write!(f, "(")?;
            for (i, arg) in self.term.iter_args().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(
                    f,
                    "{}",
                    DisplayTerm {
                        term: arg,
                        context: self.context
                    }
                )?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}

struct DisplayLiteral<'a> {
    literal: &'a Literal,
    context: &'a KernelContext,
}

impl DisplayLiteral<'_> {
    fn term<'a>(&'a self, term: &'a Term) -> DisplayTerm<'a> {
        DisplayTerm::from_term(term, self.context)
    }
}

impl fmt::Display for DisplayLiteral<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.literal.positive {
            if self.literal.is_signed_term() {
                write!(f, "{}", self.term(&self.literal.left))
            } else {
                write!(
                    f,
                    "{} = {}",
                    self.term(&self.literal.left),
                    self.term(&self.literal.right)
                )
            }
        } else if self.literal.is_signed_term() {
            write!(f, "not {}", self.term(&self.literal.left),)
        } else {
            write!(
                f,
                "{} != {}",
                self.term(&self.literal.left),
                self.term(&self.literal.right),
            )
        }
    }
}

pub struct DisplayClause<'a> {
    pub clause: &'a Clause,
    pub context: &'a KernelContext,
}

impl fmt::Display for DisplayClause<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.clause.literals.is_empty() {
            return write!(f, "<empty>");
        }
        for (i, literal) in self.clause.literals.iter().enumerate() {
            if i > 0 {
                write!(f, " or ")?;
            }
            write!(
                f,
                "{}",
                DisplayLiteral {
                    literal,
                    context: self.context
                }
            )?;
        }
        Ok(())
    }
}
