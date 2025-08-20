use tower_lsp::lsp_types::Range;

use crate::acorn_value::AcornValue;
use crate::code_generator::CodeGenerator;
use crate::environment::Environment;
use crate::module::ModuleId;
use crate::proposition::Proposition;

#[derive(Debug, Clone)]
pub struct Goal {
    pub proposition: Proposition,
}

impl Goal {
    pub fn new(proposition: Proposition) -> Self {
        Goal { proposition }
    }

    pub fn value(&self) -> &AcornValue {
        &self.proposition.value
    }

    pub fn range(&self) -> Range {
        self.proposition.source.range
    }
}

// A goal along with some information related to it.
pub struct GoalContext {
    pub module_id: ModuleId,

    // Something a person reads, describing this goal.
    pub description: String,

    // The goal itself.
    pub goal: Goal,

    // The zero-based line where we would insert a proof for this goal.
    // This is either the last line, for a goal with a block, or the first line.
    pub proof_insertion_line: u32,

    // Whether we need to insert a block, if we do insert a proof.
    pub insert_block: bool,

    // Whether it's okay if we discover an inconsistency in the provided facts.
    // If it's not okay, we warn the user.
    pub inconsistency_okay: bool,

    // This range includes the entire proof block for this goal, if there is one.
    pub first_line: u32,
    pub last_line: u32,
}

impl GoalContext {
    // env is the environment we are proving the goal in.
    pub fn new(
        env: &Environment,
        goal: Goal,
        proof_insertion_line: u32,
        first_line: u32,
        last_line: u32,
    ) -> GoalContext {
        // Goals should never be generic.
        assert!(!goal.proposition.value.has_generic());

        let description = match goal.proposition.theorem_name() {
            Some(name) => name.to_string(),
            None => CodeGenerator::new(&env.bindings)
                .value_to_code(&goal.proposition.value)
                .unwrap_or("<goal>".to_string()),
        };
        GoalContext {
            module_id: env.module_id,
            description,
            goal,
            proof_insertion_line,
            insert_block: env.implicit,
            inconsistency_okay: env.includes_explicit_false,
            first_line,
            last_line,
        }
    }
}
