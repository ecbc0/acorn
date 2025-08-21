use crate::code_generator::CodeGenerator;
use crate::environment::Environment;
use crate::module::ModuleId;
use crate::proposition::Proposition;

// A goal along with some information related to it.
#[derive(Clone, Debug)]
pub struct Goal {
    pub module_id: ModuleId,

    // Something a person reads, describing this goal.
    pub description: String,

    // The proposition to be proved.
    pub proposition: Proposition,

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

impl Goal {
    /// Creates a new Goal with the given parameters.
    fn new(
        env: &Environment,
        prop: &Proposition,
        proof_insertion_line: u32,
        first_line: u32,
        last_line: u32,
    ) -> Goal {
        // Goals should never be generic.
        assert!(!prop.value.has_generic());

        let description = match prop.theorem_name() {
            Some(name) => name.to_string(),
            None => CodeGenerator::new(&env.bindings)
                .value_to_code(&prop.value)
                .unwrap_or("<goal>".to_string()),
        };

        Goal {
            module_id: env.module_id,
            description,
            proposition: prop.clone(),
            proof_insertion_line,
            insert_block: env.implicit,
            inconsistency_okay: env.includes_explicit_false,
            first_line,
            last_line,
        }
    }

    /// Creates a Goal for a block that has a goal.
    pub fn block(env: &Environment, prop: &Proposition) -> Goal {
        let first_line = env.first_line;
        let last_line = env.last_line();
        Self::new(env, prop, last_line, first_line, last_line)
    }

    /// Creates a Goal for a proposition that is inside a block (or standalone).
    pub fn interior(env: &Environment, prop: &Proposition) -> Goal {
        let first_line = prop.source.range.start.line;
        let last_line = prop.source.range.end.line;
        Self::new(env, prop, first_line, first_line, last_line)
    }
}
