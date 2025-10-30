use crate::certificate::Certificate;
use crate::environment::Environment;
use crate::module::LoadState;
use crate::processor::Processor;
use crate::project::Project;
use crate::prover::{Outcome, ProverMode};
use crate::saturation::SaturationProver;

/// Expects the proof to succeed, and a valid concrete proof to be generated.
pub fn prove(project: &mut Project, module_name: &str, goal_name: &str) -> Certificate {
    let module_id = project
        .load_module_by_name(module_name)
        .expect("load failed");
    let load_state = project.get_module_by_id(module_id);
    let base_env = match load_state {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("module loading error: {}", e),
        _ => panic!("no module"),
    };
    let node = base_env.get_node_by_goal_name(goal_name);
    let facts = node.usable_facts(project);
    let goal = node.goal().unwrap();
    let mut processor = Processor::new();
    for fact in facts {
        processor.add_fact(fact).unwrap();
    }
    processor.set_goal(&goal).unwrap();
    let outcome = processor.search(ProverMode::Test);

    assert_eq!(outcome, Outcome::Success);
    let cursor = base_env.get_node_by_goal_name(goal_name);
    let env = cursor.goal_env().unwrap();

    let cert =
        match processor
            .prover()
            .make_cert(project, &env.bindings, processor.normalizer(), true)
        {
            Ok(cert) => cert,
            Err(e) => panic!("make_cert failed: {}", e),
        };

    if let Err(e) = processor.check_cert(&cert, None, project, &env.bindings) {
        panic!("check_cert failed: {}", e);
    }
    cert
}

// Does one proof on the provided text for a specific goal.
pub fn prove_text(text: &str, goal_name: &str) -> Outcome {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };

    // Find the specific goal by name
    for cursor in env.iter_goals() {
        let goal = cursor.goal().unwrap();
        if goal.name == goal_name {
            let facts = cursor.usable_facts(&project);

            let mut processor = Processor::new();
            for fact in facts {
                if let Err(_) = processor.add_fact(fact) {
                    return Outcome::Inconsistent;
                }
            }
            if let Err(_) = processor.set_goal(&goal) {
                return Outcome::Inconsistent;
            }

            return processor.search(ProverMode::Test);
        }
    }
    panic!("goal '{}' not found in text", goal_name);
}

// Verifies all the goals in the provided text, returning any non-Success outcome.
pub fn verify(text: &str) -> Result<Outcome, String> {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    let module_id = project.load_module_by_name("main").expect("load failed");
    let env = match project.get_module_by_id(module_id) {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("error: {}", e),
        _ => panic!("no module"),
    };
    for cursor in env.iter_goals() {
        let facts = cursor.usable_facts(&project);
        let goal = cursor.goal().unwrap();

        let mut processor = Processor::new();
        for fact in facts {
            processor.add_fact(fact)?;
        }
        processor.set_goal(&goal)?;

        // This is a key difference between our verification tests, and our real verification.
        // This helps us test that verification fails in cases where we do have an
        // infinite rabbit hole we could go down.
        let outcome = processor.search(ProverMode::Test);
        if outcome != Outcome::Success {
            return Ok(outcome);
        }
        let env = cursor.goal_env().unwrap();
        let cert = processor
            .prover()
            .make_cert(&project, &env.bindings, processor.normalizer(), true)
            .map_err(|e| e.to_string())?;
        if let Err(e) = processor.check_cert(&cert, None, &project, &env.bindings) {
            panic!("check_cert failed: {}", e);
        }
    }
    Ok(Outcome::Success)
}

pub fn verify_succeeds(text: &str) {
    let outcome = verify(text).expect("verification errored");
    if outcome != Outcome::Success {
        panic!(
            "We expected verification to return Success, but we got {}.",
            outcome
        );
    }
}

pub fn verify_fails(text: &str) {
    let outcome = verify(text).expect("verification errored");

    if outcome != Outcome::Exhausted {
        panic!(
            "We expected verification to return Exhausted, but we got {}.",
            outcome
        );
    }
}

pub const THING: &str = r#"
    type Thing: axiom
    let t: Thing = axiom
    let t2: Thing = axiom
    let f: Thing -> Bool = axiom
    let g: (Thing, Thing) -> Thing = axiom
    let h: Thing -> Thing = axiom
    "#;

// Does one proof in the "thing" environment.
pub fn prove_thing(text: &str, goal_name: &str) -> Outcome {
    let text = format!("{}\n{}", THING, text);
    prove_text(&text, goal_name)
}
