set_option pp.fieldNotation false

/- @@@

# Evidence

This material is based on

- Chapter 3 of [Concrete Semantics](http://www.concrete-semantics.org/)
- Inductive Propositions from [Software Foundations](https://softwarefoundations.cis.upenn.edu/lf-current/IndProp.html)

@@@-/

/- @@@

## The Collatz Conjecture

Per Wikipedia, the [Collatz Conjecture](https://en.wikipedia.org/wiki/Collatz_conjecture) is

> one of the most famous unsolved problems in mathematics.
> The conjecture asks whether repeating two simple arithmetic operations
> will eventually transform every positive integer into 1...
> It concerns sequences of integers where each term is obtained
> from the previous term as follows:
>
> + if a term is even, the next term is one half of it.
> + if a term is odd, the next term is 3 times the previous term plus 1.
>
> The conjecture is that these sequences always reach 1, **no matter which positive integer is chosen to start the sequence.**
>
> The conjecture has been shown to hold for all positive integers up to $$2.95 \times 10^{20}$$, but no general proof has been found.

Lets try to model the Collatz Conjecture in Lean.

A function that computes the `half` of a `Nat` and that determines if a `Nat` is `even`.
@@@ -/


def half (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | ((n + 1) + 1) => (half n) + 1

example : half 5 = 2 := by rfl
example : half 10 = 5 := by rfl

def even (n: Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | (n + 1) + 1 => even n

example : even 5  = false := by rfl
example : even 10 = true  := by rfl


/- @@@
Now, lets try to write a function that computes the **next term** in the Collatz sequence,
and use it to run the Collatz sequence starting from a given number.
@@@ -/

def collatz_step (n : Nat) : Nat :=
  if even n then half n else 3 * n + 1

def run_collatz (steps n : Nat) : List Nat :=
  match steps with
  | 0 => [n]
  | steps + 1 => n :: run_collatz steps (collatz_step n)

/- @@@
Lets try to `run_collatz` for a few numbers...
@@@ -/

#eval run_collatz 5  5
#eval run_collatz 17 15
#eval run_collatz 26 200


/- @@@

## The Termination Restriction

Can we write a function to _count_ the number of steps needed to reach 1?

@@@ -/


-- def collatz_steps (n : Nat) : Nat :=
--   match n with
--   | 1 => 1
--   | n => collatz_steps (collatz_step n) + 1

/- @@@

Welp! `lean` is unhappy with this definition as it **cannot determine the function terminates**!

All our previous examples, `lean` was fine with because the "recursion" was on "smallar inputs, e.g.
in `plus` below, in each recursive call, `n` is **getting smaller** -- we start with `n+1` and recurse on `n`
all the way till it reaches `0`, so `lean` is happy. If you have (possibly) non-terminating functions, you can
prove things like `1 = 2` which would make the whole system inconsistent (i.e. useless).
@@@ -/

def plus (n m : Nat) : Nat :=
  match n with
  | 0 => m
  | n + 1 => (plus n m) + 1

/- @@@
So: `lean` and similar provers require that all recursive functions are **provably terminating**.

How can we then even **specify** the **Collatz Conjecture** in `lean` ?

@@@ -/

/- @@@
## Idea: Inductively Defined Evidence (or Proofs)

We can specify the collatz conjecture by defining a way to explicitly
**construct evidence** that a given number `n` will eventually reach
`1` in the Collatz sequence.

For example, we know that the number `n` reaches `1` in the Collatz sequence if

* [ collatz-one ] if `n` is equal to `1`, OR
* [ collatz-evn ] if `n` is even and `half n` reaches `1`, OR
* [ collatz-odd ] if `n` is not even and `3*n + 1` reaches `1`

We can define a **datatype** whose values **represent** the above conditions.

In PL, we often write the above three rules as follows, where the

* "numerator" is the *conditions* or **hypotheses** under which the rule holds
* "denominator" is the *conclusion* or **consequence** that follows from the conditions.


```

--------------------- [collatz-one]
collatz_reaches_one 1


even n      collatz_reaches_one (half n)
---------------------------------------- [collatz-even]
collatz_reaches_one n


¬ (even n)  collatz_reaches_one (3*n + 1)
----------------------------------------- [collatz-odd]
collatz_reaches n
```

## Inductive Propositions

We can encode the above rules in `lean` as an *inductive proposition*

@@@ -/

inductive collatz_reaches_one : Nat -> Prop where
  | collatz_one : collatz_reaches_one 1
  | collatz_evn : ∀ {n : Nat}, even n -> collatz_reaches_one (half n) -> collatz_reaches_one n
  | collatz_odd : ∀ {n : Nat}, ¬ even n -> collatz_reaches_one (3*n + 1) -> collatz_reaches_one n

open collatz_reaches_one

/- @@@

Note that the above is a rather fancy data type, where, unlike `List` or `Nat`
1. the constructed "type" is `Prop` i.e. a proposition, and
2. the actual `Prop` is _different_ for the different constructors!

So, in

* The `one` case: the term `collatz_one` is an object of type `collatz_reaches_one 1`

* The `evn` case: the constructor `collatz_evn` takes as input two arguments,
  - a proof that `n` is even and
  - a proof that `half n` reaches `1`,
  and constructs a proof that `n` reaches `1`

* The `odd` case: the constructor `collatz_odd` takes as input two arguments,
  - a proof that `n` is not even and
  - a proof that `3*n + 1` reaches `1`,
  and constructs a proof that `n` reaches `1`

As an example, we can construct evidence that `5` reaches `1` in the Collatz sequence

@@@ -/

def collatz_1 : collatz_reaches_one 1 :=
  collatz_one

def collatz_2 : collatz_reaches_one 2 :=
  let even_2 : even 2 := by simp [even]
  collatz_evn even_2 (collatz_1)

def collatz_4 : collatz_reaches_one 4 :=
  let even_4 : even 4 := by simp [even]
  collatz_evn even_4 (collatz_2)

def collatz_8 : collatz_reaches_one 8 :=
  let even_8 : even 8 := by simp [even]
  collatz_evn even_8 (collatz_4)

def collatz_16 : collatz_reaches_one 16 :=
  let even_16 : even 16 := by simp [even]
  collatz_evn even_16 (collatz_8)

def collatz_5 : collatz_reaches_one 5 :=
  let odd_5 : ¬ (even 5) := by simp [even]
  collatz_odd odd_5 (collatz_16)


/- @@@
You can also construct evidence with tactics ...
@@@ -/

theorem collatz_5_tt : collatz_reaches_one 5 := by
  apply collatz_odd
  simp [even]
  apply collatz_evn
  simp [even]
  simp [half]
  apply collatz_evn
  simp [even]
  simp [half]
  apply collatz_evn
  simp [even]
  simp [half]
  apply collatz_evn
  simp [even]
  simp [half]
  apply collatz_one

/- @@@
Finally, you can **state** the Collatz conjecture as follows:
@@@ -/

theorem collatz_theorem : ∀ n, collatz_reaches_one n := by
  sorry  -- *well* out of the scope of CSE 230 ...

/- @@@

Now that we have motivated the *need* for explicit evidence, lets look at some more examples.

@@@ -/

/- @@@

## Example: Even Numbers

Lets try to define the notion of a number `n` being *even* as an inductive proposition `ev n`.

What are the rules for a number `n` to be even?







Lets try to write these rules down in `lean`...

@@@ -/

inductive ev : Nat -> Prop where
  | evZ : ev 0
  | evSS : ∀ {n: Nat}, ev n -> ev (n + 2)

open ev

/- @@@
As before, we can construct explicit evidence for a few numbers...
@@@ -/

def even_0  : ev 0 :=                  evZ
def even_2  : ev 2 :=             evSS evZ
def even_4  : ev 4 :=       evSS (evSS evZ)
def even_6  : ev 6 := evSS (evSS (evSS evZ))

/- @@@
Note that evidence is literally just a value so we can use `even_4` to get a proof of `even_6`
@@@ -/

def even_6' : ev 6 := evSS (   even_4     )


/- @@@
### Tactic: `apply`

Building up these "trees" can quickly get tiring. Tactics help! The `apply` constructor
takes the current goal and "applies" a constructor to it, thus reducing the goal to its
"hypotheses".
@@@ -/


def even_8 : ev 8 := by
  apply evSS
  apply evSS
  apply evSS
  apply evSS
  apply evZ

/- @@@
### Tactic: `constructor`

The `constructor` tactic can let you skip the name of the actual constructor,
as long as there is a particular constructor that *matches* the current goal.

(Of course, in the below you can also `repeat` the application of `constructor`).

@@@ -/

def even_8' : ev 8 := by
  constructor
  constructor
  constructor
  constructor
  constructor

/- @@@
### Tactic: `solve_by_elim`

The `solve_by_elim` tactic is even funner: it can do a bit of "search" by recursively `apply`-ing
the appropriate constructors (upto some fixed search depth.)
@@@ -/

def even_8'' : ev 8 := by
  solve_by_elim



/- @@@
## Constructing / Producing Evidence

Lets try to prove that if `even n` returns `true`,
then we can construct evidence that `ev n`.

@@@ -/

theorem even_ev : ∀ {n : Nat}, even n = true -> ev n := by
  intros n h
/- @@@ START:SORRY @@@ -/
  induction n using even.induct
  case case1 => constructor
  case case2 => contradiction
  case case3 n' ih' => simp_all [even]; constructor; assumption
/- @@@ END:SORRY @@@ -/

/- @@@
## Destructing / Using Evidence

Next, lets try to prove the opposite: whenever
we have evidence that `ev n`, we can prove that
`even n = true`!

How can we possibly prove this?
@@@ -/

theorem ev_even : ∀ {n : Nat}, ev n -> even n = true := by
/- @@@ START:SORRY @@@ -/
  intros n h
  induction h
  case evZ  => rfl
  case evSS => simp [even, *]
/- @@@ END:SORRY @@@ -/


/- @@@
## Example: Reflexive, Transitive Closure

Suppose we have a datatype to represent some set of persons

@@@ -/

inductive person : Type where
  | alice   : person
  | bob     : person
  | charlie : person
  | diane   : person
  | esther  : person
  | fred    : person
  | gerald  : person
  | harry   : person

open person

/- @@@

we can define a relation `parent_of` that specifies some relationship between two `person`s.

@@@ -/

inductive parent_of : person -> person -> Prop where
  | parent_ab : parent_of alice   bob
  | parent_bc : parent_of bob     charlie
  | parent_cd : parent_of charlie diane
  | parent_ef : parent_of esther  fred
  | parent_fg : parent_of fred    gerald
  | parent_gh : parent_of gerald  fred

open parent_of

/- @@@

Now suppose we want to define an `ancestor_of` relationship, as

- **(reflexive)** `x` is an `ancestor_of `x` or
- **(transitive)** if `parent_of x z` and `ancestor_of x z` then `ancestor_of x z`

That is, the `ancestor_of` relation is the **reflexive** and **transitive**
closure of a relation `parent_of`.

Suppose that `r` is a binary relation on `α`  i.e. some fact that holds on two `α`.

The reflexive transitive closure of `r` is defined as the relation `rr` where

- (**reflexive**) `rr x x` i.e. `rr` relates every element `x` to itself,
- (**transitive**) if `r x y` and  `rr y z` then `rr x z`

Lets define this as an inductive proposition

@@@ -/

inductive star {α : Type} (r: α -> α -> Prop) : α -> α -> Prop where
  | refl : ∀ {a : α}, star r a a
  | step : ∀ {x y z : α}, r x y -> star r y z -> star r x z

open star

/- @@@
We can now define `ancestor_of` using `star`, and then test it out on a few examples.
@@@ -/

abbrev ancestor_of := star parent_of

example : ancestor_of alice alice := by
  sorry

example : ancestor_of alice diane := by
  sorry

example : ancestor_of esther fred := by
  sorry


/- @@@

If you think about it, if

- if `a` is an `ancestor_of` some person `b`,
- and `b` is an `ancestor_of` some person `c`

then

- `a` should _also_ be an `ancestor_of `c` ?

In fact, this **transitivity** fact should hold for *any* `star r`. Lets try to prove it!

**HINT:** The `solve_by_elim` tactic is quite handy.

@@@ -/

theorem star_trans : ∀ {α : Type} {r : α -> α -> Prop} {a b c : α},
  star r a b -> star r b c -> star r a c :=
  by
  sorry


/- @@@

## Example: Grammars and Parsing

Lets look at one last example of doing induction on evidence. Consider two grammars
for parsing strings over the characters `a` and `b`

The first grammar is defined by the non-terminal `S`

```
  S ::= ε | a S b | S S
```

The second grammar is defined by the non-terminal `T`

```
  T ::= ε | T a T b
```

Do these grammars accept the same set of strings?


@@@ -/


inductive Alphabet where
  | a : Alphabet
  | b : Alphabet
  deriving Repr

open Alphabet

inductive gS : List Alphabet -> Prop where
   | gS0 : gS []
   | gS1 : ∀ {s : List Alphabet}, gS s -> gS (a :: s ++ [b])
   | gS2 : ∀ {s1 s2 : List Alphabet}, gS s1 -> gS s2 -> gS (s1 ++ s2)
open gS

inductive gT : List Alphabet -> Prop where
  | gT0 : gT []
  | gT1 : ∀ {t1 t2 : List Alphabet}, gT t1 -> gT t2 -> gT (t1 ++ ([a] ++ t2 ++ [b]))
open gT

/- @@@

**Exercise:** Try to prove that the two grammars are equivalent,
that is complete the proofs of `S_imp_T` and `T_imp_S` below.
(Start with `T_imp_S`)

@@@-/

/- @@@ START:CUT @@@ -/
theorem T_append : ∀ {s1 s2 : List Alphabet}, gT s1 -> gT s2 -> gT (s1 ++ s2) := by
  intros s1 s2 T_s1 T_s2
  induction T_s2
  case gT0 => simp [List.append_nil]; assumption
  case gT1 t1' t2' _ _ _ _ =>
    have h : (s1 ++ (t1' ++ ([a] ++ t2' ++ [b]))) = (s1 ++ t1' ++ ([a] ++ t2' ++ [b])) := by simp [List.append_assoc]
    rw [h]
    constructor
    assumption
    assumption
/- @@@ END:CUT @@@ -/

theorem S_imp_T : ∀ {w : List Alphabet}, gS w -> gT w := by
/- @@@ START:SORRY @@@ -/
  intros _ gs
  induction gs
  case gS0 => constructor
  case gS1 => apply (gT1 gT0); assumption
  case gS2 _ s1 s2 _ _ T_s1 T_s2 => apply T_append <;> assumption
/- @@@ END:SORRY @@@ -/

theorem T_imp_S : ∀ {w : List Alphabet}, gT w -> gS w := by
/- @@@ START:SORRY @@@ -/
  intros _ gt
  induction gt
  case gT0 => constructor
  case gT1 => constructor
              . case _ => simp_all [] -- assumption
              . case _ => constructor
                          simp_all [List.append]
/- @@@ END:SORRY @@@ -/

theorem S_equiv_T : ∀ {w : List Alphabet}, gS w ↔ gT w := by
  intros w
  constructor
  apply S_imp_T
  apply T_imp_S
