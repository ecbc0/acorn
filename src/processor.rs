use std::borrow::Cow;

use crate::binding_map::BindingMap;
use crate::builder::BuildError;
use crate::certificate::Certificate;
use crate::checker::{Checker, StepReason};
use crate::code_generator::Error;
use crate::fact::Fact;
use crate::goal::Goal;
use crate::normalizer::Normalizer;
use crate::project::Project;
use crate::proof_step::Rule;
use crate::saturation::{Outcome, Prover, ProverParams};
use tokio_util::sync::CancellationToken;

/// The processor represents all of the stuff that can accept a stream of facts.
/// We might want to rename this or refactor it away later.
#[derive(Clone)]
pub struct Processor {
    prover: Prover,
    normalizer: Normalizer,
    checker: Checker,
}

impl Processor {
    pub fn new() -> Processor {
        Processor {
            prover: Prover::new(vec![]),
            normalizer: Normalizer::new(),
            checker: Checker::new_fast(),
        }
    }

    pub fn with_token(cancellation_token: CancellationToken) -> Processor {
        Processor {
            prover: Prover::new(vec![cancellation_token]),
            normalizer: Normalizer::new(),
            checker: Checker::new_fast(),
        }
    }

    pub fn with_dual_tokens(token1: CancellationToken, token2: CancellationToken) -> Processor {
        Processor {
            prover: Prover::new(vec![token1, token2]),
            normalizer: Normalizer::new(),
            checker: Checker::new_fast(),
        }
    }

    pub fn prover(&self) -> &Prover {
        &self.prover
    }

    pub fn normalizer(&self) -> &Normalizer {
        &self.normalizer
    }

    /// Normalizes a fact and adds the resulting proof steps to the prover.
    pub fn add_fact(&mut self, fact: Fact) -> Result<(), BuildError> {
        let steps = self.normalizer.normalize_fact(fact)?;
        for step in &steps {
            // Extract the source from the step's rule.
            // When monomorphizing, the step contains the source of the general fact being specialized,
            // not the source of the specific theorem invoking it.
            let step_source = match &step.rule {
                Rule::Assumption(info) => info.source.clone(),
                _ => {
                    return Err(BuildError::new(
                        Default::default(),
                        format!(
                            "Expected assumption step from normalize_fact, got: {:?}",
                            step.rule
                        ),
                    ));
                }
            };
            self.checker
                .insert_clause(&step.clause, StepReason::Assumption(step_source));
        }
        self.prover.add_steps(steps);
        Ok(())
    }

    /// Normalizes a goal and sets it as the prover's goal.
    pub fn set_goal(&mut self, goal: &Goal) -> Result<(), BuildError> {
        let source = &goal.proposition.source;
        let (ng, steps) = self.normalizer.normalize_goal(goal)?;
        for step in &steps {
            // Use the step's own source if it's an assumption (which includes negated goals),
            // otherwise use the goal's source
            let step_source = if let crate::proof_step::Rule::Assumption(info) = &step.rule {
                &info.source
            } else {
                source
            };
            self.checker
                .insert_clause(&step.clause, StepReason::Assumption(step_source.clone()));
        }
        self.prover.set_goal(ng, steps);
        Ok(())
    }

    /// Forwards a search request to the underlying prover.
    pub fn search(&mut self, params: ProverParams) -> Outcome {
        self.prover.search(params)
    }

    /// Creates a certificate from the current proof state.
    pub fn make_cert(
        &self,
        project: &Project,
        bindings: &BindingMap,
        print: bool,
    ) -> Result<Certificate, Error> {
        self.prover
            .make_cert(project, bindings, &self.normalizer, print)
    }

    /// Checks a certificate by cloning the checker and normalizer, and creating a Cow for bindings.
    /// This encapsulates the pattern used throughout the codebase.
    /// If the goal is provided, it is added to the checker before checking the certificate.
    /// Returns a list of CertificateSteps showing how each step was verified.
    pub fn check_cert(
        &self,
        cert: &Certificate,
        goal: Option<&Goal>,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<Vec<crate::checker::CertificateStep>, Error> {
        let mut checker = self.checker.clone();
        let mut normalizer = self.normalizer.clone();

        if let Some(goal) = goal {
            let source = &goal.proposition.source;
            let (_, steps) = normalizer.normalize_goal(goal).map_err(|e| e.message)?;
            for step in &steps {
                // Use the step's own source if it's an assumption (which includes negated goals),
                // otherwise use the goal's source
                let step_source = if let crate::proof_step::Rule::Assumption(info) = &step.rule {
                    &info.source
                } else {
                    source
                };
                checker.insert_clause(&step.clause, StepReason::Assumption(step_source.clone()));
            }
        }

        let mut bindings = Cow::Borrowed(bindings);
        checker.check_cert(cert, project, &mut bindings, &mut normalizer)
    }
}
