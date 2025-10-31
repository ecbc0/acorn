use std::fmt;

use crate::acorn_type::{AcornType, TypeParam};
use crate::acorn_value::AcornValue;
use crate::compilation::{self, ErrorSource};
use crate::names::ConstantName;

/// A generic constant that we don't know the type of yet.
/// It's more of a "constant with unresolved type" than an "unresolved constant".
#[derive(Debug, Clone, PartialEq)]
pub struct UnresolvedConstant {
    /// The global name of the constant.
    pub name: ConstantName,

    /// The type parameters are all the type variables used in the definition of this constant,
    /// in their canonical order. Each of these type parameters should be referenced in the type of
    /// the constant itself. Otherwise we would not be able to infer them.
    pub params: Vec<TypeParam>,

    /// The generic type uses the params.
    pub generic_type: AcornType,

    /// Arguments that have been partially applied to this constant.
    /// When this is resolved, these arguments will be applied to the resolved value.
    pub args: Vec<AcornValue>,
}

impl UnresolvedConstant {
    /// Resolves the constant with the given parameters.
    pub fn resolve(
        &self,
        source: &dyn ErrorSource,
        params: Vec<AcornType>,
    ) -> compilation::Result<AcornValue> {
        if params.len() != self.params.len() {
            return Err(source.error(&format!(
                "expected {} type parameters, but got {}",
                self.params.len(),
                params.len()
            )));
        }

        let named_params: Vec<_> = self
            .params
            .iter()
            .zip(params.iter())
            .map(|(param, t)| (param.name.clone(), t.clone()))
            .collect();
        let resolved_type = self.generic_type.instantiate(&named_params);
        let mut value = AcornValue::constant(self.name.clone(), params, resolved_type);

        // Apply any stored arguments
        if !self.args.is_empty() {
            value = AcornValue::apply(value, self.args.clone());
        }

        Ok(value)
    }

    /// Turn this into a constant value by keeping each parameter as a type variable.
    pub fn to_generic_value(self) -> AcornValue {
        let params = self
            .params
            .iter()
            .map(|p| AcornType::Variable(p.clone()))
            .collect();
        let mut value = AcornValue::constant(self.name.clone(), params, self.generic_type);

        // Apply any stored arguments
        if !self.args.is_empty() {
            value = AcornValue::apply(value, self.args);
        }

        value
    }
}

impl fmt::Display for UnresolvedConstant {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.name)?;
        if !self.params.is_empty() {
            write!(f, "[")?;
            for (i, param) in self.params.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", param.name)?;
            }
            write!(f, "]")?;
        }
        if !self.args.is_empty() {
            write!(f, "(")?;
            for (i, arg) in self.args.iter().enumerate() {
                if i > 0 {
                    write!(f, ", ")?;
                }
                write!(f, "{}", arg)?;
            }
            write!(f, ")")?;
        }
        Ok(())
    }
}
