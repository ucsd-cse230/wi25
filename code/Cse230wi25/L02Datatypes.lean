

/- @@@
# Datatypes and Recursion

This material is based on sections 5,6 of [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/getting-to-know.html)

## Datatypes

So far, we saw some "primitive" or "built-in" types like `Nat`, `Bool` etc.

The "primitive" `Bool` type is actually defined as a datatype in the standard library:

The type has two constructors
- `Bool.false`
- `Bool.true`.

Which you can think of as "enum"-like constructors.

Like all (decent) modern languages, Lean lets you **construct**
new kinds of datatypes. Let's redefine `Bool` locally, just to
see how it's done.

@@@ -/

namespace MyBool

inductive Bool : Type where
  | false : Bool
  | true  : Bool
  deriving Repr

#eval Bool.true


/- @@@

## Pattern Matching

The constructors let us _produce_ or _build_ values of the datatype.

The *only* way to get a `Bool` is by using the `Bool.true` or `Bool.false` constructors.

In contrast, **pattern-matching** lets us _consume_ or _use_ the values of that datatype...

Lets write a function `neg` that takes a `Bool` and returns the opposite `Bool`, that is

* when given `Bool.true`,  `neg` should return `Bool.false`
* when given `Bool.false`, `neg` should return `Bool.true`

@@@ -/

def neg (b: Bool) :=
  match b with
  | Bool.true  => Bool.false
  | Bool.false => Bool.true

/- @@@

Lets test it to make sure the right thing is happening

@@@ -/

#eval neg Bool.true
#eval neg Bool.false

/- @@@

Our first "theorem" ... let us prove that `neg true` _is_ `false` by

1. defining a **variable** `neg_true_eq_false` (you can call it whatever you like...)
2. whose **type is the proposition** `neg Bool.true = Bool.false` we want to "prove"
3. whose **body is the proof** of the proposition.

For now, lets just write `by sorry` for the "proof".



@@@ -/

def neg_b_neq : ∀ (b:Bool), ¬ (neg b = b) := by
  intros b
  cases b <;> simp [neg]

def neg_neg_b_eq : ∀ (b:Bool), neg (neg b) = b := by
  intros b
  cases b <;> simp [neg]

def neg_true_eq_false : neg Bool.true = Bool.false := by
  rfl

/- @@@

foo <;> bar

## Goals

How shall we write the proof?

Well, you can see the _goal_ by

1. putting the cursor next to the `by` (before `sorry`)
2. looking at the `Lean Infoview` on the right in vscode

![Viewing the Goal](../static/L02_neg_true_eq_false_sorry.png)

A *goal* always looks like `h1, h2, h3, ... ⊢ g` where

- `h1`, `h2`, `h3` etc. are **hypotheses** i.e. *what we have*, and
- `<g>` is the **goal** i.e. *what we want* to prove.

In this case, the hypotheses are empty and the goal is `neg Bool.true = Bool.false`.

@@@ -/

/- @@@
## Tactics

Proofs can be difficult to write (in this case, not so much).

Fortunately, `lean` will help us *build up* the proof by

- giving us the _goal_ that
- we can gradually simplify, split ...
- till we get simple enough sub-goals that it can solve automatically.


**TACTIC `rfl`:** The most basic tactic is `rfl` which abbreviates
*reflexivity*, which is a fancy way of saying "evaluate the lhs and
rhs and check if they are equal".

**EXERCISE:** Write down and "prove" the theorem that `neg false` is `true`.

**EXERCISE** What other "facts" can you think up (and prove!) about `neg`?

@@@ -/











/- @@@

Next, lets try to prove a fact about how `neg`
behaves on *all* `Bool` values. For example,
lets try to prove that when we `neg` a `Bool`
value `b` *two* times we get back `b`.

@@@ -/


def neg_neg : ∀ (b: Bool), neg (neg b) = b := by
  sorry








/- @@@
This time we cannot just use `rfl` -- try it and see what happens!

In its own way, `lean` is saying "I can't tell you (evaluate) what `neg b`
is because I don't know what `b` is!"

**TACTIC `intros`:** First, we want to use the `intros` tactic which will "move"
the `∀ (b: Bool)` from the *goal* into a plain `b : Bool` hypothesis.
That is, the `intros` tactic will change the goal from
`∀ (b: Bool), neg (neg b) = b` to `b : Bool ⊢ neg (neg b) = b`,
meaning that our task is now to prove that `neg (neg b) = b`
*assuming* that `b` is some `Bool` valued thing.

Of course, we still cannot use `rfl` because lean does not know what
`neg b` until `b` itself has some concrete value.

**TACTIC `cases`:** The path forward in this case is to use the `cases` tactic
which does a *case analysis* on `b`, i.e. tells `lean` to *split cases* on each
of the possible values of `b` --- when it is `true` and when it is `false`.
Now, when you put your cursor next to `cases b` you see the *two* subgoals
- **`case false`** which is `⊢ neg (neg Bool.false) = Bool.false`
- **`case true`**  which is `⊢ neg (neg Bool.true) = Bool.true`

Each case (subgoal) can be proved by `rfl` so you can complete the proof as


@@@ -/

def neg_neg_1 : ∀ (b : Bool), neg (neg b) = b := by
  intros b
  cases b
  rfl
  rfl

/- @@@

However, I prefer to make the different subgoals more "explicit" by writing

@@@ -/

def neg_neg_2 : ∀ (b : Bool), neg (neg b) = b := by
  intros b
  cases b
  . case false => rfl
  . case true => rfl


/- @@@
**Conjunction** Lets write an `and` function that
- takes two `Bool`s and
- returns a `Bool` that is `true` if *both* are `true` and `false` otherwise.
@@@ -/

def and (b1 b2: Bool) : Bool :=
  match b1, b2 with
  | Bool.true, Bool.true => Bool.true
  | _        , _         => Bool.false


/- @@@

**`and` is Commutative** Lets try to prove that `and`
is *commutative*, i.e. `and b1 b2 = and b2 b1`.
You can start off with `intros` and then use `cases`
as before, but we may have to do case analysis on *both*
the inputs!

@@@ -/


theorem and_comm : ∀ (b1 b2 : Bool), and b1 b2 = and b2 b1 := by
  sorry

/- @@@

**TACTIC COMBINATOR `<;>`:** It is a bit tedious to repeat the *same* sub-proof so many times!
The `foo <;> bar` tactic combinator lets you chain tactics together so by first applying `foo`
and then applying `bar` *to each* sub-goal generated by `foo`. We can use `<;>` to considerably
simplify the proof. In the proof below, move your mouse over the `cases b1 <;> cases b2 <;> ...`
line and see how the goals change in the `Lean Infoview` panel.

@@@ -/

theorem and_comm' : ∀ (b1 b2 : Bool), and b1 b2 = and b2 b1 := by
  -- use the <;> tactic combinator
  sorry

/- @@@

**Disjunction** Lets write an `or` function that
- takes two `Bool`s and
- returns a `Bool` that is `true` if *either* is `true` and `false` otherwise.

@@@ -/

def or (b1 b2: Bool) : Bool := sorry

/- @@@

**EXERCISE** Complete the proof of the theorem that `or` is commutative,
i.e. `or` produces the same result no matter the order of the arguments.

@@@ -/

theorem or_comm : ∀ (b1 b2 : Bool), or b1 b2 = or b2 b1 := by
  sorry

end MyBool


/- @@@

## Recursion**

`Bool` is a rather simple type that has just *two* elements --- `true` and `false`.

Pretty much all proofs about `Bool` can be done by splitting `cases` on the relevant `Bool`
values and then running `rfl` (i.e. via a giant "case analysis").

Next, lets look at a more interesting type, which has an **infinite** number of values.
@@@ -/

namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
  deriving Repr

open Nat

/- @@@

## Zero, One, Two, Three, ... infinity

Unlike `Bool` there are *infinitely* many `Nat` values.

@@@ -/

def n0 : Nat :=                  zero
def n1 : Nat :=             succ zero
def n2 : Nat :=       succ (succ zero)
def n3 : Nat := succ (succ (succ zero))

/- @@@

This has *two* related consequences.

First, we cannot write interesting functions over `Nat`
just by brute-force *enumerating* the inputs and outputs
as we did with `and` and `or`; instead we will have to
use **recursion**.

Second, we cannot write interesting proofs over `Nat`
just by brute-force *case-splitting* over the values
as we did with `and_comm` and `or_comm`; instead we will
have to use **induction**.

## Addition

Lets write a function to *add* two `Nat` values.
@@@ -/

def add (n m: Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)

example : add n1 n2 = n3 := by rfl

/- @@@
## Adding Zero

Next, lets try to prove some simple facts about `add` for example
@@@ -/

theorem add_zero_left : ∀ (n: Nat), add zero n = n := by
  intros
  rfl

/- @@@
The proof of `add_zero_left` is super easy because it is literally
(part of) the **definition** of `add` which tells `lean` that it obeys
two **equations**

    add zero      m = m
    add (succ n') m = succ (add n' m)

So the `rfl` applies the first equation and boom we're done.

## Adding Zero on the _Right_

However, lets see what happens if we flip the order of the arguments,
so that the *second* argument is `zero`

@@@ -/

theorem add_zero' : ∀ (n: Nat), add n zero = n := by
  intros n
  sorry

/- @@@
Boo! Now the proof fails because the equation does not apply!

## "Calculation" or "Equational Reasoning"

In fact, lets us try to see *why* the theorem is even true,
slowly working our way up the `Nat` numbers.

```
  add zero  zero
    { by def of add }
    ===> zero                     ... (0)

  add (succ zero) zero
    { by def of add }
    ===> succ (add zero zero)
    { by (0) }
    ===> succ zero                ... (1)

  add (succ (succ (zero))) zero
    { by def }
    ===> succ (add (succ zero) zero)
    { by (1) }
    ===> succ (succ zero)         ... (2)

  add (succ (succ (succ (zero)))) zero
    { by def }
    ===> succ (add (succ (succ zero)) zero)
    { by (2) }
    ===> succ (succ (succ zero))  ... (3)
```

## `calc` mode

`lean` has a neat `calc` mode that lets us write
the above proofs (except, they are actually *checked!*)

@@@ -/

theorem add_0 : add zero zero = zero := by
  calc
    add zero zero = zero := by simp [add] -- just apply the

theorem add_1 : add (succ zero) zero = succ zero := by
  calc
    add (succ zero) zero
      = succ (add zero zero) := by simp [add]
    _ = succ zero            := by simp [add_0]

theorem add_2 : add (succ (succ zero)) zero = succ (succ zero) := by
  calc
    add (succ (succ zero)) zero
      = succ (add (succ zero) zero) := by simp [add]
    _ = succ (succ zero)            := by simp [add_1]

theorem add_3 : add (succ (succ (succ zero))) zero = succ (succ (succ zero)) := by
  calc
    add (succ (succ (succ zero))) zero
      = succ (add (succ (succ zero)) zero) := by simp [add]
    _ = succ (succ (succ zero))            := by simp [add_2]

/-@@@

## Proof by Induction

Notice that *each* of the proofs above is basically the same:

To prove the fact `add_{n+1}` we
1. apply the *definition* of `add` and then
2. *recursively* use the fact `add_{n}`!

### Recursion

Lets us *define* `add` **for each** `Nat` by *reusing* the definitions on **smaller** numbers

### Induction

Lets us *prove* `add_n` **for each** `Nat` by *reusing* the proofs on **smaller** numbers

@@@ -/

theorem add_zero : ∀ (n: Nat), add n zero = n := by
  intros n
  induction n
  . case zero       => simp [add]
  . case succ n' ih => simp [add, ih]

end MyNat

/- @@@

## Polymorphism

@@@ -/


namespace MyList

inductive List (α : Type) where
  | nil : List α
  | cons : α -> List α -> List α
  deriving Repr

open List

def list0123 := cons 0 (cons 1 (cons 2 (cons 3 nil)))
def list3210 := cons 3 (cons 2 (cons 1 (cons 0 nil)))

def app {α : Type} (xs ys: List α) : List α :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (app xs' ys)

example : app (cons 0 (cons 1 nil)) (cons 2 (cons 3 nil)) = list0123 := by
  simp [app, list0123]


example : app (cons 0 (cons 1 nil)) (cons 2 (cons 3 nil)) = cons 0 (cons 1 (cons 2 (cons 3 nil))) := rfl

theorem app_nil : ∀ {α : Type} (xs: List α), app xs nil = xs := by
  intro α xs
  induction xs
  case nil => rfl
  case cons => simp [app, *]

theorem app_assoc : ∀ {α : Type} (xs ys zs: List α), app (app xs ys) zs = app xs (app ys zs) := by
  intros  α xs ys zs
  induction xs
  case nil => rfl
  case cons => simp [app, *]


end MyList
