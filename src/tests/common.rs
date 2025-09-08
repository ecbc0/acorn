use std::borrow::Cow;

use crate::certificate::Certificate;
use crate::code_generator::Error;
use crate::environment::Environment;
use crate::module::LoadState;
use crate::normalizer::Normalizer;
use crate::project::Project;
use crate::prover::{Outcome, Prover};

// Helper to do a proof for a particular goal.
fn prove_helper<'a>(
    project: &'a mut Project,
    module_name: &str,
    goal_name: &str,
) -> (&'a Project, &'a Environment, Prover, Normalizer, Outcome) {
    let module_id = project
        .load_module_by_name(module_name)
        .expect("load failed");
    let load_state = project.get_module_by_id(module_id);
    let env = match load_state {
        LoadState::Ok(env) => env,
        LoadState::Error(e) => panic!("module loading error: {}", e),
        _ => panic!("no module"),
    };
    let node = env.get_node_by_goal_name(goal_name);
    let facts = node.usable_facts(project);
    let goal = node.goal().unwrap();
    let mut prover = Prover::new(&project);
    let mut normalizer = Normalizer::new();
    for fact in facts {
        let steps = normalizer.normalize_fact(fact).unwrap();
        prover.add_steps(steps);
    }
    let (ng, steps) = normalizer.normalize_goal(&goal).unwrap();
    prover.set_goal(ng, steps);
    prover.strict_codegen = true;
    let outcome = prover.quick_search();
    (project, env, prover, normalizer, outcome)
}

// Tries to prove one thing from the project.
// If the proof is successful, try to generate the code.
pub fn prove_with_old_codegen(
    project: &mut Project,
    module_name: &str,
    goal_name: &str,
) -> (Prover, Normalizer, Outcome, Result<Vec<String>, Error>) {
    let (project, env, prover, normalizer, outcome) = prove_helper(project, module_name, goal_name);
    let code = match prover.get_condensed_proof(&normalizer) {
        Some(proof) => {
            prover.print_proof(&proof, project, &env.bindings, &normalizer);
            proof.to_code(&env.bindings)
        }
        None => {
            println!("we do not have a proof");
            Err(Error::NoProof)
        }
    };
    (prover, normalizer, outcome, code)
}

/// Expects the proof to succeed, and a valid concrete proof to be generated.
pub fn prove(project: &mut Project, module_name: &str, goal_name: &str) -> Certificate {
    let (project, base_env, prover, normalizer, outcome) =
        prove_helper(project, module_name, goal_name);
    assert_eq!(outcome, Outcome::Success);
    let cursor = base_env.get_node_by_goal_name(goal_name);
    let env = cursor.goal_env().unwrap();

    let cert = match prover.make_cert(project, &env.bindings, &normalizer, true) {
        Ok(cert) => cert,
        Err(e) => panic!("make_cert failed: {}", e),
    };

    let mut checker = prover.checker.clone();
    let mut normalizer = normalizer.clone();
    let mut bindings = Cow::Borrowed(&env.bindings);
    if let Err(e) = checker.check_cert(&cert, project, &mut bindings, &mut normalizer) {
        panic!("check_cert failed: {}", e);
    }
    cert
}

pub fn prove_as_main(
    text: &str,
    goal_name: &str,
) -> (Prover, Normalizer, Outcome, Result<Vec<String>, Error>) {
    let mut project = Project::new_mock();
    project.mock("/mock/main.ac", text);
    prove_with_old_codegen(&mut project, "main", goal_name)
}

// Does one proof on the provided text.
pub fn prove_text(text: &str, goal_name: &str) -> Outcome {
    let (_prover, _normalizer, outcome, _code) = prove_as_main(text, goal_name);
    outcome
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
        println!("proving: {}", goal.name);

        let mut prover = Prover::new(&project);
        let mut normalizer = Normalizer::new();
        for fact in facts {
            let steps = normalizer.normalize_fact(fact)?;
            prover.add_steps(steps);
        }
        let (ng, steps) = normalizer.normalize_goal(&goal)?;
        prover.set_goal(ng, steps);

        // This is a key difference between our verification tests, and our real verification.
        // This helps us test that verification fails in cases where we do have an
        // infinite rabbit hole we could go down.
        let outcome = prover.quick_shallow_search();
        if outcome != Outcome::Success {
            return Ok(outcome);
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

pub fn expect_proof(text: &str, goal_name: &str, expected: &[&str]) {
    let (_prover, _normalizer, outcome, code) = prove_as_main(text, goal_name);
    assert_eq!(outcome, Outcome::Success);
    let actual = code.expect("code generation failed");
    assert_eq!(actual, expected);
}

// Expects the prover to find a proof that's one of the provided ones.
pub fn expect_proof_in(text: &str, goal_name: &str, expected: &[&[&str]]) {
    let (_prover, _normalizer, outcome, code) = prove_as_main(text, goal_name);
    assert_eq!(outcome, Outcome::Success);
    let actual = code.expect("code generation failed");

    // There's multiple things it could be that would be fine.
    for e in expected {
        if actual == *e {
            return;
        }
    }

    println!("unexpected code:");
    for line in &actual {
        println!("{}", line);
    }
    panic!("as vec: {:?}", actual);
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
