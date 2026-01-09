use crate::elaborator::environment::Environment;
use crate::normalizer::Normalizer;

#[test]
fn test_nat_normalization() {
    let mut env = Environment::test();
    let mut norm = Normalizer::new();
    env.add("type Nat: axiom");
    env.add("let zero: Nat = axiom");
    env.expect_type("zero", "Nat");
    env.add("let suc: Nat -> Nat = axiom");
    env.expect_type("suc", "Nat -> Nat");
    env.add("let one: Nat = suc(zero)");
    env.expect_type("one", "Nat");

    env.add("axiom suc_injective(x: Nat, y: Nat) { suc(x) = suc(y) implies x = y }");
    norm.check(&env, "suc_injective", &["suc(x0) != suc(x1) or x0 = x1"]);
    env.expect_type("suc_injective", "(Nat, Nat) -> Bool");

    env.add("axiom suc_neq_zero(x: Nat) { suc(x) != zero }");
    norm.check(&env, "suc_neq_zero", &["zero != suc(x0)"]);
    env.expect_type("suc_neq_zero", "Nat -> Bool");

    env.add(
        "axiom induction(f: Nat -> Bool) {\
        f(zero) and forall(k: Nat) { f(k) implies f(suc(k)) } implies forall(n: Nat) { f(n) } }",
    );

    norm.check(
        &env,
        "induction",
        &[
            "not x0(zero) or x0(s0(x0)) or x0(x1)",
            "not x0(suc(s0(x0))) or not x0(zero) or x0(x1)",
        ],
    );

    env.expect_type("induction", "(Nat -> Bool) -> Bool");

    env.add("define recursion(f: Nat -> Nat, a: Nat, n: Nat) -> Nat { axiom }");
    env.expect_type("recursion", "(Nat -> Nat, Nat, Nat) -> Nat");

    env.add("axiom recursion_base(f: Nat -> Nat, a: Nat) { recursion(f, a, zero) = a }");
    env.expect_type("recursion_base", "(Nat -> Nat, Nat) -> Bool");
    norm.check(&env, "recursion_base", &["recursion(x0, x1, zero) = x1"]);

    env.add(
        "axiom recursion_step(f: Nat -> Nat, a: Nat, n: Nat) {\
        recursion(f, a, suc(n)) = f(recursion(f, a, n)) }",
    );
    env.expect_type("recursion_step", "(Nat -> Nat, Nat, Nat) -> Bool");
    norm.check(
        &env,
        "recursion_step",
        &["recursion(x0, x1, suc(x2)) = x0(recursion(x0, x1, x2))"],
    );
}

#[test]
fn test_bool_formulas() {
    let mut env = Environment::test();
    let mut norm = Normalizer::new();
    env.add("theorem one(a: Bool) { a implies a or (a or a) }");
    norm.check(&env, "one", &["not x0 or x0"]);

    env.add("theorem two(a: Bool) { a implies a and (a and a) }");
    norm.check(
        &env,
        "two",
        &["not x0 or x0", "not x0 or x0", "not x0 or x0"],
    );
}

#[test]
fn test_tautology_elimination() {
    let mut env = Environment::test();
    let mut norm = Normalizer::new();
    env.add("type Nat: axiom");
    env.add("theorem one(n: Nat) { n = n }");
    norm.check(&env, "one", &[]);

    env.add("theorem two(n: Nat) { n = n or n != n }");
    norm.check(&env, "two", &[]);
}

#[test]
fn test_nested_skolemization() {
    let mut env = Environment::test();
    let mut norm = Normalizer::new();
    env.add("type Nat: axiom");
    env.add("theorem exists_eq(x: Nat) { exists(y: Nat) { x = y } }");
    norm.check(&env, "exists_eq", &["s0(x0) = x0"]);
}

#[test]
fn test_second_order_binding() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let borf: (Nat, Nat, Nat) -> Bool = axiom
        define also_borf(a: Nat, b: Nat, c: Nat) -> Bool { borf(a, b, c) }
        let bb: Nat = axiom
        let cc: Nat = axiom
        define specific_borf(x: Nat) -> Bool { also_borf(x, bb, cc) }
        define always_true(f: Nat -> Bool) -> Bool { forall(n: Nat) { f(n) } }
        theorem goal { not always_true(specific_borf) }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["not always_true(specific_borf)"]);
}

#[test]
fn test_boolean_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let n0: Nat = axiom
        let n1: Nat = axiom
        let n2: Nat = axiom
        let n3: Nat = axiom
        theorem goal { (n0 = n1) = (n2 = n3) }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["n1 != n0 or n3 = n2", "n3 != n2 or n1 = n0"],
    );
}

#[test]
fn test_boolean_inequality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let n0: Nat = axiom
        let n1: Nat = axiom
        let n2: Nat = axiom
        let n3: Nat = axiom
        theorem goal { (n0 = n1) != (n2 = n3) }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["n3 != n2 or n1 != n0", "n3 = n2 or n1 = n0"],
    );
}

#[test]
fn test_functions_returning_lambdas() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let addx: (Nat, Nat) -> Nat = axiom
        define adder(a: Nat) -> (Nat -> Nat) { function(b: Nat) { addx(a, b) } }
        theorem goal(a: Nat, b: Nat) { adder(a)(b) = adder(b)(a) }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["adder(x0, x1) = adder(x1, x0)"]);
}

#[test]
fn test_functional_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        define zerof(a: Nat) -> (Nat -> Nat) { function(b: Nat) { zero } }
        theorem goal(a: Nat, b: Nat) { zerof(a) = zerof(b) }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["zerof(x0, x1) = zerof(x2, x1)"]);
}

#[test]
fn test_normalizing_exists() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        let addx: (Nat, Nat) -> Nat = axiom
        theorem goal { exists(x: Nat) { addx(x, zero) = one } }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["addx(s0, zero) = one"]);
}

#[test]
fn test_denormalizing_disjunction() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        let ltx: (Nat, Nat) -> Bool = axiom
        let addx: (Nat, Nat) -> Nat = axiom
        theorem foo(x0: Nat, x1: Nat) { addx(addx(x0, zero), x1) != zero or ltx(x1, zero) }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "foo",
        &["addx(addx(x0, zero), x1) != zero or ltx(x1, zero)"],
    );
}

#[test]
fn test_functional_skolemization() {
    // This matches a pattern that failed in finite_constraint proving
    let mut env = Environment::test();
    env.add(
        r#"
        type T: axiom
        type List: axiom
        let contains: (List, T) -> Bool = axiom
        define finite_constraint(p: T -> Bool) -> Bool {
            exists(lst: List) {
                forall(x: T) {
                    p(x) implies contains(lst, x)
                }
            }
        }
        theorem test_finite(p: T -> Bool) {
            not finite_constraint(p) or
            exists(lst: List) {
                forall(x: T) {
                    p(x) implies contains(lst, x)
                }
            }
        }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "test_finite",
        &["not finite_constraint(x0) or not x0(x1) or contains(s0(x0), x1)"],
    );
}

#[test]
fn test_if_then_else_under_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let c: Bool = axiom
        let d: Bool = axiom

        theorem goal {
            a = if b {
                c
            } else {
                d
            }
        }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &[
            "not b or not a or c",
            "not a or d or b",
            "not c or not b or a",
            "not d or b or a",
        ],
    );
}

#[test]
fn test_if_then_else_with_true_branch_under_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        let a: Bool = axiom
        let b: Bool = axiom
        let d: Bool = axiom

        theorem goal {
            a = if b {
                true
            } else {
                d
            }
        }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["not a or d or b", "not b or a", "not d or b or a"],
    );
}

#[test]
fn test_if_then_else_normalization_with_variables() {
    let mut env = Environment::test();
    env.add(
        r#"
        type T: axiom
        let foo: (T -> Bool, T, T) -> Bool = axiom

        theorem goal(f: T -> Bool, item: T, x: T) {
            foo(f, item, x) = if x = item {
                true
            } else {
                f(x)
            }
        }
        "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &[
            "not foo(x0, x1, x2) or x1 = x2 or x0(x2)",
            "x0 != x1 or foo(x2, x0, x1)",
            "not x0(x1) or foo(x0, x2, x1) or x1 = x2",
        ],
    );
}

#[test]
fn test_lambda_normalization() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f1: (Nat, Nat) -> Nat = axiom
        let f2: (Nat, Nat) -> Nat = axiom

        theorem goal {
            forall(a: Nat) {
                f1(a) = function(b: Nat) {
                    f2(a)(b)
                }
            }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["f2(x0, x1) = f1(x0, x1)"]);
}

#[test]
fn test_normalizing_functional_or() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom
        let h: Nat -> Bool = axiom
        let dis: Nat -> Bool = axiom

        theorem goal(a: Nat) {
            dis(a) = (f(a) or g(a) or h(a))
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &[
            "not dis(x0) or h(x0) or g(x0) or f(x0)",
            "not f(x0) or dis(x0)",
            "not g(x0) or dis(x0)",
            "not h(x0) or dis(x0)",
        ],
    );
}

#[test]
fn test_normalizing_equals_exists() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let b: Bool = axiom
        let f: Nat -> Bool = axiom

        theorem goal {
            b = exists(x: Nat) {
                f(x)
            }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["not b or f(s0)", "not f(x0) or b"]);
}

#[test]
fn test_normalizing_not_or_exists() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            not (exists(x: Nat) {
                f(x)
            } or exists(y: Nat) {
                g(y)
            })
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["not f(x0)", "not g(x0)"]);
}

#[test]
fn test_normalizing_exists_inside_if() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let b: Bool = axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            if b {
                exists(x: Nat) { f(x) }
            } else {
                exists(y: Nat) { g(y) }
            }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["not b or f(s0)", "g(s1) or b"]);
}

#[test]
fn test_normalizing_lambda_inside_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let z: Nat = axiom
        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Nat = axiom
        let h: (Nat, Nat) -> Nat = axiom

        theorem goal(a: Nat) {
            f(a) = function(b: Nat) {
                g(h(a, b)) = z
            }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &[
            "not f(x0, x1) or g(h(x0, x1)) = z",
            "g(h(x0, x1)) != z or f(x0, x1)",
        ],
    );
}

#[test]
fn test_normalizing_function_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Nat = axiom
        let g: (Nat, Nat) -> Nat = axiom
        let a: Nat = axiom

        theorem goal {
            f = g(a)
        }
    "#,
    );
    let mut norm = Normalizer::new();
    // We need to add the expanded version here because we don't have the types
    // in the prover.
    norm.check(&env, "goal", &["g(a, x0) = f(x0)", "g(a) = f"]);
}

#[test]
fn test_normalizing_function_inequality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Nat = axiom
        let g: (Nat, Nat) -> Nat = axiom
        let a: Nat = axiom

        theorem goal {
            f != g(a)
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["g(a, s0) != f(s0)"]);
}

#[test]
fn test_normalizing_func_eq_inside_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: Nat -> Bool = axiom
        let g: (Nat, Nat) -> Nat = axiom
        let h: (Nat, Nat) -> Nat = axiom

        theorem goal {
            f = function(x: Nat) {
                g(x) = h(x)
            }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &[
            "not f(x0) or h(x0, x1) = g(x0, x1)",
            "h(x0, s0(x0)) != g(x0, s0(x0)) or f(x0)",
        ],
    );
}

#[test]
fn test_normalizing_exists_inside_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            g = function(x: Nat) {
                    exists(y: Nat) {
                        f(x, y)
                    }
                }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["not g(x0) or f(x0, s0(x0))", "not f(x0, x1) or g(x0)"],
    );
}

#[test]
fn test_normalizing_forall_inside_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            g = function(x: Nat) {
                    forall(y: Nat) {
                        f(x, y)
                    }
                }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["not g(x0) or f(x0, x1)", "not f(x0, s0(x0)) or g(x0)"],
    );
}

#[test]
fn test_normalizing_exists_inside_neq_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            g != function(x: Nat) {
                    exists(y: Nat) {
                        f(x, y)
                    }
                }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["not f(s0, x0) or not g(s0)", "f(s0, s1) or g(s0)"],
    );
}

#[test]
fn test_normalizing_forall_inside_neq_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            g != function(x: Nat) {
                    forall(y: Nat) {
                        f(x, y)
                    }
                }
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["not f(s0, s1) or not g(s0)", "f(s0, x0) or g(s0)"],
    );
}

#[test]
fn test_normalizing_pre_expanded_exists_inside_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom

        let f: (Nat, Nat) -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal(a: Nat) {
            g(a) = function(x: Nat) {
                        exists(y: Nat) {
                            f(x, y)
                        }
                    }(a)
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &["not g(x0) or f(x0, s0(x0))", "not f(x0, x1) or g(x0)"],
    );
}

#[test]
fn test_normalizing_boolean_function_equality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            f = g
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["g(x0) = f(x0)", "g = f"]);
}

#[test]
fn test_normalizing_boolean_function_inequality() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let f: Nat -> Bool = axiom
        let g: Nat -> Bool = axiom

        theorem goal {
            f != g
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["g(s0) != f(s0)"]);
}

#[test]
fn test_normalizing_lambda_applied_to_lambda() {
    let mut env = Environment::test();
    env.add(
        r#"
        type Foo: axiom
        let a: Foo = axiom
        let b: Foo = axiom
        let g: (Foo, Foo) -> Bool = axiom

        theorem goal {
            function(f: Foo -> Bool) {
                f(a)
            }(
                function(x: Foo) {
                    g(x, b)
                }
            )
        }
    "#,
    );
    let mut norm = Normalizer::new();
    norm.check(&env, "goal", &["g(a, b)"]);
}

#[test]
fn test_normalizing_and_inside_arg() {
    let mut env = Environment::test();
    env.add(
        r#"
        structure BoxedBool {
            value: Bool
        }

        let f: (BoxedBool, BoxedBool) -> BoxedBool = axiom

        theorem goal {
            f = function(a: BoxedBool, b: BoxedBool) {
                BoxedBool.new(a.value and b.value)
            }
        }
    "#,
    );

    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &[
            "not s0(x0, x1) or BoxedBool.value(x0)",
            "not s0(x0, x1) or BoxedBool.value(x1)",
            "not BoxedBool.value(x0) or not BoxedBool.value(x1) or s0(x0, x1)",
            "BoxedBool.new(s0(x0, x1)) = f(x0, x1)",
        ],
    );
}

#[test]
fn test_normalizing_nested_lambdas() {
    let mut env = Environment::test();
    env.add(
        r#"
    type Nat: axiom
    type ListNat: axiom
    let range: Nat -> ListNat = axiom
    let sum: ListNat -> Nat = axiom
    let map: (ListNat, Nat -> Nat) -> ListNat = axiom

    define double_sum(n: Nat, m: Nat, f: (Nat, Nat) -> Nat) -> Nat {
        sum(map(range(n), function(i: Nat) {
            sum(map(range(m), function(j: Nat) { f(i, j) }))
        }))
    }

    theorem goal(a: Nat, b: Nat, f: (Nat, Nat) -> Nat) {
        double_sum(a, b, f) = sum(map(range(a), function(i: Nat) {
            sum(map(range(b), function(j: Nat) { f(i, j) }))
        }))
    }
    "#,
    );

    let mut norm = Normalizer::new();
    norm.check(
        &env,
        "goal",
        &[
            "sum(map(range(x0), s1(x1, x0, x2, x3))) = s0(x1, x0, x2, x3)",
            "s1(x0, x1, x2, x3, x4) = x2(x3, x4)",
            "sum(map(range(x0), s0(x0, x1, x2))) = double_sum(x0, x1, x2)",
        ],
    );
}

#[test]
fn test_if_then_else_with_forall_condition() {
    // Test that if-then-else with a forall in the condition works correctly.
    // This exercises a code path where forall variables need their types tracked
    // in the context. The forall body is a conjunction so that it produces non-literal CNF.
    let mut env = Environment::test();
    env.add(
        r#"
        type Nat: axiom
        let zero: Nat = axiom
        let one: Nat = axiom
        let p: Nat -> Bool = axiom
        let q: Nat -> Bool = axiom

        theorem goal {
            if forall(n: Nat) { p(n) and q(n) } {
                zero
            } else {
                one
            } = zero
        }
        "#,
    );
    let mut norm = Normalizer::new();
    // The key thing is that normalization doesn't panic - the forall variable's type must be
    // properly tracked in the context when creating clauses.
    norm.check(
        &env,
        "goal",
        &[
            "not s0 or p(x0)",
            "not s0 or q(x0)",
            "not q(x0) or not p(x0) or s0",
            "one = zero or s0",
        ],
    );
}

/// Test that normalizing a polymorphic theorem with type parameters in the goal doesn't crash.
/// This test catches a bug where the LocalContext was empty when clause normalization tried
/// to remap variables for type parameters.
#[test]
#[cfg(feature = "polymorphic")]
fn test_polymorphic_type_params_in_goal() {
    let mut env = Environment::test();
    env.add(
        r#"
        // Define a simple identity function with two equivalent definitions
        define id1[T](x: T) -> T { x }
        define id2[T](x: T) -> T { x }

        // This theorem has type parameter [T] that appears directly in the goal
        theorem id_equivalence[T] {
            id1[T] = id2[T]
        }
        "#,
    );
    let mut norm = Normalizer::new();
    // We don't check the exact clauses - we just verify normalization doesn't crash
    let clauses = norm.get_all_clauses(&env);
    assert!(!clauses.is_empty(), "Should have normalized clauses");
}
