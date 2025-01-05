# Useful Lean4 Tactics

See [this document](https://leanprover.github.io/theorem_proving_in_lean4/tactics.html) for more details on Lean4 tactics.

## `rfl`

(from `claude`)

The `rfl` tactic in Lean 4 stands for "reflexivity"
and proves equality goals by simplification and
checking that both sides are syntactically equal.
For example:

```lean
example : 2 + 2 = 4 := by rfl
```

`rfl` will:

1. Reduce both sides of the equality to their **normal form** using computation
2. Check if the results are exactly the same
3. If they match, the proof is complete

This tactic is useful for equality goals where the two
sub-expressions become identical after computation.

However, `rfl` **will not work** if the equality requires
any non-trivial reasoning (e.g. induction) or if the terms
are not **syntactically equal** after reduction.

```lean
-- this works
example : 2 + 1 + x = 1 + 1 + 1 + x  := by rfl

-- but this does not work
example : 2 + 1 + x = 1 + 1 + x + 1  := by rfl
```

## `simp`

The `simp` tactic performs simplification using
a set of pre-registered lemmas and definitions.
Specifically, `simp [foo, bar, baz]` will use
the equalities of `foo`, `bar`, and `baz` to
simplify the goal into a form where those equalities
can no longer be applied.

For example, suppose we want to prove that
for any two natural numbers `a` and `b`,
if `a = b`, then `a + a = b + b`.

```lean
example (a b : Nat) (h : a = b) : a + a = b + b := by
  simp [h]
```

In the above proof, we use the `simp` tactic
to simplify the goal `a + a = b + b` using the
hypothesis `a = b` into `b + b = b + b`, which
then simplifies to `true`.
