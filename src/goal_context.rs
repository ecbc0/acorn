use crate::code_generator::CodeGenerator;
use crate::goal::Goal;
use crate::project::Project;

/// Context information for an AI to help with theorem proving.
/// Contains relevant code snippets and goal information.
#[derive(Clone, Debug)]
pub struct GoalContext {
    /// Everything before first_line in the document
    pub prefix_lines: String,

    /// Lines from first_line through last_line (the goal itself)
    pub goal_lines: String,

    /// Stringified version of the hypothesis from negate_goal.
    /// Empty string if there is none.
    pub hypothesis: String,

    /// Stringified version of the counterfactual from negate_goal
    pub counterfactual: String,
}

impl GoalContext {
    /// Generate a GoalContext from a Project and Goal.
    /// Returns None if we can't read the file or generate the context.
    pub fn from_project_and_goal(project: &Project, goal: &Goal) -> Option<Self> {
        // Get the module's file path
        let path = project.path_from_module_id(goal.module_id)?;

        // This properly handles both open files in memory and filesystem files
        let content = project.read_file(&path).ok()?;

        // Split into lines
        let lines: Vec<&str> = content.lines().collect();

        // Extract prefix_lines (everything before first_line)
        let prefix_lines = if goal.first_line > 0 {
            lines[..goal.first_line as usize].join("\n")
        } else {
            String::new()
        };

        // Extract goal_lines (first_line through last_line)
        let goal_lines = if goal.last_line as usize >= lines.len() {
            lines[goal.first_line as usize..].join("\n")
        } else {
            lines[goal.first_line as usize..=goal.last_line as usize].join("\n")
        };

        // Negate the goal to get hypothesis and counterfactual
        let (hypothesis_value, counterfactual_value) = goal.proposition.value.clone().negate_goal();

        // Get the environment for code generation
        let env = project.get_env_by_id(goal.module_id)?;
        let mut code_gen = CodeGenerator::new(&env.bindings);

        // Stringify the hypothesis (if it exists)
        let hypothesis = if let Some(hyp) = hypothesis_value {
            code_gen.value_to_code(&hyp).ok()?
        } else {
            String::new()
        };

        // Stringify the counterfactual
        let counterfactual = code_gen.value_to_code(&counterfactual_value).ok()?;

        Some(GoalContext {
            prefix_lines,
            goal_lines,
            hypothesis,
            counterfactual,
        })
    }
}
