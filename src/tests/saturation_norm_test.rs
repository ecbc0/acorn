use super::common::*;

// This file tests that normalization works correctly, by proving statements that require normalization to prove.

#[test]
fn test_proving_with_boxed_bool() {
    let text = r#"
    structure BoxedBool {
        value: Bool
    }

    define boxed_and(a: BoxedBool, b: BoxedBool) -> BoxedBool {
        BoxedBool.new(a.value and b.value)
    }

    theorem goal(b: BoxedBool) {
        not b.value implies not boxed_and(b, b).value
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_avoids_infinitely_nested_types() {
    let text = r#"
        structure Set[K] {
            contains: K -> Bool
        }

        structure Pair[K1, K2] {
            first: K1
            second: K2
        }

        define elem_in_product[K1,K2](a1: Set[K1], a2: Set[K2], p: Pair[K1,K2]) -> Bool {
            a1.contains(p.first) and a2.contains(p.second)
        }

        attributes Set[K1] {
            define mul[K2](self, a: Set[K2]) -> Set[Pair[K1,K2]] {
                Set[Pair[K1,K2]].new(elem_in_product(self, a))
            }
        }

        // This theorem monomorphizes into indefinitely nested types if if you don't limit it.
        theorem foo_5[K, L](a: Set[K], b1: Set[L], b2: Set[L]) {
            a.mul(b1).mul(b2) = a.mul(b1).mul(b2)
        }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_proving_avoids_infinite_monomorphization_recursion() {
    // This is a regression test to ensure we don't crash when processing
    // nested generic attribute calls with multiple type parameters.
    // The theorem is not provable, but we should handle it gracefully.
    let text = r#"

    inductive List<T> {
        nil
        cons(T, List<T>)
    }

    attributes List<T> {
        define map<U>(self, f: T -> U) -> List<U> {
            match self {
                List.nil {
                    List.nil<U>
                }
                List.cons(head, tail) {
                    List.cons(f(head), tail.map(f))
                }
            }
        }
    }

    theorem foo_1<T, U>(items: List<T>, f: T -> U, g: U -> U, items_1: List<U>) {
        items.map(f).map(g) = items_1
    }
    "#;
    // This should not crash, even though the theorem is not provable
    verify_fails(text);
}

#[test]
fn test_proving_avoids_another_infinite_monomorphization_recursion() {
    let text = r#"
    structure Set[K] {
        contains: K -> Bool
    }

    define constant_false[K](x: K) -> Bool {
        false
    }

    attributes Set[K] {
        let empty_set = Set[K].new(constant_false[K])
    }

    structure Map[K, L] {
        in_space: Set[K]
        out_space: Set[L]
        fn: K -> L
    }

    attributes Map[K, L] {
        define is_surjective(self) -> Bool {
            forall(y: L) {
                self.out_space.contains(y) implies exists(x: K) {
                    self.in_space.contains(x) and self.fn(x) = y
                }
            }
        }
    }

    /// the set theory version of product_index
    define elem_in_product_index_map[I, K](m: Map[I, Set[K]], x: I -> K) -> Bool {
        forall(i: I) {
            m.in_space.contains(i) implies m.fn(i).contains(x(i))
        }
    }

    // We should be able to prove the goal, but this definition introduced new
    // types and causes an infinite recursion. (At the time the bug was reported.)
    define product_index_map[I, K](m: Map[I, Set[K]]) -> Set[I -> K] {
        Set[I -> K].new(elem_in_product_index_map(m))
    }

    attributes Set[K] {
        define superset(self, a: Set[K]) -> Set[K] {
            forall(x: K) {
                a.contains(x) implies self.contains(x)
            }
        }
    }

    define power_set[K](a: Set[K]) -> Set[Set[K]] {
        Set[Set[K]].new(a.superset)
    }

    type Nat: axiom

    attributes Set[K] {
        define is_finite_set(self) -> Bool {
            if self = Set[K].empty_set {
                true
            } else {
                exists(num: Nat, m: Map[Nat, K]) {
                    m.out_space = self
                }
            }
        }
    }

    theorem goal[K] {
        exists(s: Set[K]) {
            s.is_finite_set
        }
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_function_as_argument() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom

    define foo(f: Thing -> Bool) -> Bool {
        true
    }

    theorem goal {
        foo(function(t: Thing) { t = u })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_function_equality() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom
    let f: (Thing -> Bool) -> Thing = axiom

    theorem goal {
        f(function(t: Thing) { t = u }) = f(function(t: Thing) { t = u })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_const_false() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom
    define not_apply_u(t: Thing -> Bool) -> Bool {
        not t(u)
    }

    theorem anon_const_false {
        not_apply_u(function(t: Thing) { false })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_anonymous_const_true() {
    let text = r#"
    type Thing: axiom
    let u: Thing = axiom
    define not_apply_u(t: Thing -> Bool) -> Bool {
        not t(u)
    }

    theorem anon_const_false {
        not not_apply_u(function(t: Thing) { true })
    }
    "#;
    verify_succeeds(text);
}

#[test]
fn test_more_anonymous_const_false() {
    let text = r#"
    structure Set[T] {
        contains: T -> Bool
    }

    attributes Set[K] {
        let ee = Set[K].new(function(x: K) { false })
    }

    theorem goal[K] {
        exists(d: Set[K]) {
            d = Set[K].ee
        }
    }
    "#;
    verify_succeeds(text);
}
