use crate::code_generator::CodeGenerator;
use crate::goal::Goal;
use crate::project::Project;

/// Context information for an AI to help with theorem proving.
/// Contains relevant code snippets and goal information.
#[derive(Clone, Debug)]
pub struct GoalContext {
    /// Lines from the start of the enclosing theorem to the line before the goal.
    /// None if all relevant context is already in goal_lines.
    pub theorem_prefix_lines: Option<Vec<String>>,

    /// Lines from first_line through last_line (the goal itself)
    pub goal_lines: Vec<String>,

    /// Stringified version of the hypothesis from negate_goal.
    /// None if there is no hypothesis.
    pub hypothesis: Option<String>,

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

        // Get the environment for the goal's line to find the enclosing theorem
        let env = project.get_env_by_id(goal.module_id)?;
        let env_for_goal = env.env_for_line(goal.first_line);
        let theorem_first_line = env_for_goal.first_line;

        // Extract goal_lines (first_line through last_line)
        let goal_lines: Vec<String> = if goal.last_line as usize >= lines.len() {
            lines[goal.first_line as usize..]
                .iter()
                .map(|s| s.to_string())
                .collect()
        } else {
            lines[goal.first_line as usize..=goal.last_line as usize]
                .iter()
                .map(|s| s.to_string())
                .collect()
        };

        // Extract prefix_lines (from theorem start to before the goal)
        // Only include if the theorem starts before the goal
        let prefix_lines = if theorem_first_line < goal.first_line {
            let prefix: Vec<String> = lines[theorem_first_line as usize..goal.first_line as usize]
                .iter()
                .map(|s| s.to_string())
                .collect();
            Some(prefix)
        } else {
            None
        };

        // Negate the goal to get hypothesis and counterfactual
        let (hypothesis_value, counterfactual_value) = goal.proposition.value.clone().negate_goal();

        let mut code_gen = CodeGenerator::new(&env.bindings);

        // Stringify the hypothesis (if it exists)
        let hypothesis = if let Some(hyp) = hypothesis_value {
            Some(code_gen.value_to_code(&hyp).ok()?)
        } else {
            None
        };

        // Stringify the counterfactual
        let counterfactual = code_gen.value_to_code(&counterfactual_value).ok()?;

        Some(GoalContext {
            theorem_prefix_lines: prefix_lines,
            goal_lines,
            hypothesis,
            counterfactual,
        })
    }
}
