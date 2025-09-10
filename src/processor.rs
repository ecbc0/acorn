use std::borrow::Cow;

use crate::binding_map::BindingMap;
use crate::builder::BuildError;
use crate::certificate::Certificate;
use crate::checker::Checker;
use crate::code_generator::Error;
use crate::fact::Fact;
use crate::goal::Goal;
use crate::normalizer::Normalizer;
use crate::project::Project;
use crate::proof::Proof;
use crate::prover::Prover;

/// The processor represents all of the stuff that can accept a stream of facts.
/// We might want to rename this or refactor it away later.
/// At the time of writing this comment, its primary motivation for existing is
/// to handle the yaml -> jsonl build migration.
#[derive(Clone)]
pub struct Processor {
    pub prover: Prover,
    pub normalizer: Normalizer,
    pub checker: Checker,
}

impl Processor {
    /// Creates a new Processor that has a Prover.
    pub fn with_prover(project: &Project) -> Processor {
        Processor {
            prover: Prover::new(project),
            normalizer: Normalizer::new(),
            checker: Checker::new(),
        }
    }

    /// Creates a new Processor that does not have a Prover.
    pub fn without_prover() -> Processor {
        todo!();
    }

    /// Normalizes a fact and adds the resulting proof steps to the prover.
    pub fn add_fact(&mut self, fact: Fact) -> Result<(), BuildError> {
        let steps = self.normalizer.normalize_fact(fact)?;
        for step in &steps {
            self.checker.insert_clause(&step.clause);
        }
        self.prover.add_steps(steps);
        Ok(())
    }

    /// Normalizes a goal and sets it as the prover's goal.
    pub fn set_goal(&mut self, goal: &Goal) -> Result<(), BuildError> {
        let (ng, steps) = self.normalizer.normalize_goal(goal)?;
        for step in &steps {
            self.checker.insert_clause(&step.clause);
        }
        self.prover.set_goal(ng, steps);
        Ok(())
    }

    /// Gets the condensed proof from the prover using the normalizer.
    pub fn get_condensed_proof(&self) -> Option<Proof> {
        self.prover.get_condensed_proof(&self.normalizer)
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
    pub fn check_cert(
        &self,
        cert: &Certificate,
        project: &Project,
        bindings: &BindingMap,
    ) -> Result<(), Error> {
        let mut checker = self.checker.clone();
        let mut normalizer = self.normalizer.clone();
        let mut bindings = Cow::Borrowed(bindings);
        checker.check_cert(cert, project, &mut bindings, &mut normalizer)
    }
}
