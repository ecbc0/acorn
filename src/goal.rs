use crate::code_generator::CodeGenerator;
use crate::environment::Environment;
use crate::module::ModuleId;
use crate::proposition::Proposition;

// A goal along with some information related to it.
#[derive(Clone, Debug)]
pub struct Goal {
    pub module_id: ModuleId,

    // A normalized form of the goal.
    pub name: String,

    // The proposition to be proved.
    pub proposition: Proposition,

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
        first_line: u32,
        last_line: u32,
    ) -> Result<Goal, String> {
        // Goals should never be generic.
        assert!(!prop.value.has_generic());

        let name = if let Some(name) = prop.theorem_name() {
            name.to_string()
        } else {
            CodeGenerator::new(&env.bindings)
                .value_to_code(&prop.value)
                .map_err(|e| e.to_string())?
        };

        Ok(Goal {
            module_id: env.module_id,
            name,
            proposition: prop.clone(),
            insert_block: env.implicit,
            inconsistency_okay: env.includes_explicit_false,
            first_line,
            last_line,
        })
    }

    /// Creates a Goal for a block that has a goal.
    pub fn block(env: &Environment, prop: &Proposition) -> Result<Goal, String> {
        let first_line = env.first_line;
        let last_line = env.last_line();
        Self::new(env, prop, first_line, last_line)
    }

    /// Creates a Goal for a proposition that is inside a block (or standalone).
    pub fn interior(env: &Environment, prop: &Proposition) -> Result<Goal, String> {
        let first_line = prop.source.range.start.line;
        let last_line = prop.source.range.end.line;
        Self::new(env, prop, first_line, last_line)
    }
}
