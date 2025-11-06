# The road to dependent types

## Philosophy on planning itself

There are two big categories of things we need to do. First, we need to make the AI better, and second, the language needs to support all of the mathematics that people want to write. The AI part of things is tough to plan in too much detail, because it's all experimental. We need to try little things and see what works.

Language features are more straightforward to plan. So that's what this roadmap focuses on. And there is one feature that is more requested than anything else: dependent types.

## Why we need uninhabited types before dependent types

Right now, every type in Acorn must be inhabited. Ie, for every type, there must be some element of that type. The prover implicitly uses this fact to combine statements like

```
forall(x: T) {
    f(x)
}

forall(x: T) {
    not f(x)
}
```

If `T` is inhabited, this leads to a contradiction. But if `T` is not inhabited, both of these statements are vacuously true! Allowing uninhabited types means we need to do more bookkeeping to make sure we only apply this sort of deduction rule for inhabited types.

So far, disallowing uninhabited types has not been too bothersome because uninhabited types are not very interesting on their own. But this will change because with dependent types it is much less obvious when a type is inhabited. For example, a very useful dependent type is `Fin[k]` which means all natural numbers less than `k`. Note that `Fin[0]` is uninhabited. To allow expressions with `Fin[k]`, we either have to allow uninhabited types, or require that in every place we use `Fin[k]` we first prove that `k > 0`, which seems both more complicated and not how mathematicians think about the problem.

## Why we need options before uninhabited types

If uninhabited types are allowed, the current behavior of constructors of constrained types won't work. Currently, when a type is defined like

```
structure Foo {
    bar: Bar
} constraint {
    qux(bar)
}
```

If `qux(bar)` is false, the expression `Foo.new(bar)` is still a valid expression of type `Foo`, it is just a `Foo` about which nothing is known. Like a C++ "undefined behavior". This is a bit weird, but currently it's mathematically okay. But if `Foo` is uninhabited, it's no longer okay for `Foo.new(bar)` to represent a `Foo` at all. We will need to change the behavior of `new` for constrained types.

The logical meaning of a constructor for a constrained type is an option. The declaration above could become syntactic sugar for:

```
define Foo.new_eq(bar: Bar, opt: Option[Foo]) -> Bool {
    match opt {
        Option.some(foo) {
            qux(bar) and foo.bar = bar
        }
        Option.none {
            not qux(bar)
        }
    }
}

let Foo.new(bar: Bar) -> opt: Option[Foo] satisfy {
    Foo.new_eq(bar, opt)
}
```

Ie, instead of returning a nonsense `Foo` when the constraint is false, the constructor could return an option that encodes whether the constraint is true or not.

## The actual roadmap

At a high level, we need to build these things in the order of, options, uninhabited types, dependent types. At a lower level, here are some bullet points.

### A "core" module

If we have basic language syntax using options then we either need to import option all the time or make it automatically imported. Probably just automatically import it. Not rocket science but still something that logistically needs to happen.

### Make constrained types use options

This also requires a migration of the existing code. Not sure how tricky that will be.

### Inhabited typeclass

We need a typeclass that indicates that a type is inhabited. This needs to go in "core".

### Proving typeclass extension

Currently one typeclass can extend another, but only when it's defined that way. In practice, one typeclass often extends another even when it is not defined that way. In particular, many typeclasses will extend Inhabited, and we're going to need to prove that. So we will need some syntax for this, perhaps

```
extends Ring: Inhabited
```

### Allow uninhabited types

Once we have the `Inhabited` typeclass, instead of just assuming a type is inhabited, the prover should check the typeclass relationship. (This is why `Inhabited` needs to go in "core", because the prover isn't going to be able to function sanely if it isn't in the proving environment.)

### Side quest: generic let-satisfy

It would be great to define methods like:

```
let pick_any[T](list: List[T]) -> item: T satisfy {
    if list.length > 0 {
        list.contains(item)
    }
} by {
  // Proof here
}
```

However, this code is similar to the constructor of a constrained type, in that it lets you introduce terms of type `T` with no precondition, thus implicitly assuming that the type is inhabited. Once we have a clean way to handle uninhabited types, we can just check that `T` is inhabited here before allowing this syntax.

### Make a higher-order unifier

Currently, the unifier and the term representation used by the unifier are "first order", meaning that they only handles base types. There is a normalization phase in which every type gets a numeric id, and the unifier only operates on these ids.

With dependent types, there will be some expressions that cannot be normalized into a first order term. For example:

```
forall(k: Nat) {
  forall(x: Fin[k]) {
    foo(k) implies bar(x)
  }
}
```

This can't be converted into a first term because `k` appears both in "value space" and in "type space".

So we need a different term representation here. This is tricky primarily not because of the algorithm (unifying types is not much different than unifying values) but because of performance, because term manipulation is currently the performance bottleneck. Right now we are doing a huge number of tiny allocations so it might be better to redesign the term object rather than add on even more tiny allocations for the types.

### Get rid of the monomorphizer

Proving happens in two stages right now. First the monomorphizer creates first-order versions of every generic theorem, then the prover operates on the first-order terms. Once we have a higher-order unifier we shouldn't need a separate monomorphization stage, which will make it simpler to expand the type system.

### Side quest: generic instances

Relations like:

```
instance NonZero[F: Field]: Group
```

Currently that would require changing how the monomorphizer works, but once we are not monomorphizing we only have to handle this during unification, which is easier.

### Dependent types

After all that stuff, the actual implementation of dependent types should be pretty straightforward. It's just a type where one of the parameters is a value instead of a type.

We do need to figure out a syntax that can handle things like defining:

```
Fin[k]

Zmod[k]

Vector[Real, k]
```

What else?

## Open Questions

### Question mark syntax.

It seems nice to be able to do

```
let first_plus_last = list.first? + list.last?
```

Here the `?` requires proving that its argument is not none. Like syntactic sugar for

```
let Option.some(first) = list.first
let Option.some(last) = list.last
let first_plus_last = first + last
```

This way you can deal with options that happen inside an expression, not just options that happen inside a statement.

One issue is that the current prover is bad at proving "foo and bar" type goals. The harness could just give the prover one goal at a time when this happens. But we would need to change the interface so that a point in the code could be associated with multiple goals.

Another issue is that syntactically, not every expression can be associated with a proving goal, so this
syntax wouldn't be usable everywhere, which would lead to some confusion.

Another possibility would be to implement a more general solution, a way of expressing when one type could be converted into another type, and treat this as a case of converting an `Option[T]` into a `T`.
