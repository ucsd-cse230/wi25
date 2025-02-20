```lean
import Cse230wi25.BigStep
import Cse230wi25.L05Evidence

set_option pp.fieldNotation false
set_option pp.proofs true

open Aexp
open Bexp
open Com
```



# Small Step Semantics

The *big-step* semantics we've seen so far lets us write `⟨ c, s ⟩ ==> t`
to mean that when `c:Com` starts executing from `s:State` it can terminate
execution in `t:State`.

This style of defining what a program *means* was quite useful in that it
let us derive:

1. A way of proving when two *families of* programs are *equivalent*
2. A way of proving assertions about *particular* programs, via Floyd-Hoare logic.

However, the *big-step* semantics do not give us any visibility into
what happens "in the middle", e.g. as the execution marches along from
`s` to `t`.

Sometimes we care about the intermediate **sequence of steps** because

1. maybe the program **does not terminate** and still we want to know that
   nothing "bad" happens during execution, or

2. we want to reason about some low-level operations (e.g. system calls)
   that happen during the execution, and not just the start/final states, or

3. we want to reason about *concurrent* executions where we need to talk about
   the fine-grained interleaved executions of different threads.


## Strategy

So instead of saying `⟨ c, s ⟩ ==> t` we want to model executions as a series

```
c₀ -> c₁ -> c₂ -> c₃ -> ...
```

where

1. Each `cᵢ` is a `Configuration` i.e. a snapshot of the entire system,
2. Each `cᵢ -> cⱼ` is a `SmallStep`, and we can
3. Link the individual step to arbitrarily long sequences of `SmallSteps`.

So our **strategy** has three parts, we have to define a notion of

(1) `Configuration`
(2) `SmallStep`
(3) `SmallSteps`

### IMP

Can you think about how we might do this in `lean` for our IMP language

```
c ::= SKIP | x <~ a | c1 ;; c2 | IF b c1 c2 | WHILE b c
```

### Example

Suppose we have a program like

```
x <~ 10;; y <~ x + 1 ;; z <~ y + 2
```

What do you think the sequence of configurations `c₀ -> ...` might look like?










## An IMP `Configuration`

To define a small-step semantics the `Configuration` must have **all** the information
needed to determine the "next" thing that the program does. This means, a configuration
should include both

1. the **state** that maps each `Vname` to its `Value` (as in the `BigStep` semantics), *and*
2. some representation of the **remaining instructions** to execute next.

We can model the latter in several ways?

- An "instruction memory" that stores the whole program plus
  a program counter indicating current instruction?

- Just store the **remainder** of the program!

We opt for the second option as simpler for IMP:
a `Configuration` is just a *pair* (or *tuple*)
of the **remainder** `Com` and variables' `State`


```lean
abbrev Configuration := (Com × State)
```

### Example

Lets return to our original example:


```lean
abbrev com₀ : Com := x <~ 10;; (y <~ x + 1 ;; z <~ y + 2)
```

Suppose we want to execute the program from some starting
state `st₀` where all the variables are `0`


```lean
def st₀ : State := λ _ => 0
```


What are the sequence `c₀ -> c₁ -> c₂ -> c₃` of `Configuration` that we might expect?


```lean
def c₀ : Configuration := sorry
def c₁ : Configuration := sorry
def c₂ : Configuration := sorry
def c₃ : Configuration := sorry
```


## One `SmallStep`

Next, lets try to work out the rules that *define* the `SmallStep` relation.
As usual, lets use the *rules* style formulation which says that *if* the stuff
above the line holds, *then* the stuff below the line holds as well.

**Skip**

```
???
------------------------- [skip]
(Skip, s) -> ???
```

**Assign**

```
???
------------------------- [assign]
(x <~ a, s) -> ???
```

**Sequence**

```
???
------------------------- [seq]
(c1;;c2, s) -> ???
```

**If**

```
bval b s = true
--------------------------------- [if-true]
(IF b THEN c1 ELSE c2, s) -> ???
```

```
bval b s = false
--------------------------------- [if-false]
(IF b THEN c1 ELSE c2, s) -> ???
```

**While**

```
???
-------------------------- [while]
(WHILE b DO c, s) -> ???
```

Next, lets formulate the above as an `inductive SmallStep` relation:


```lean
inductive SmallStep : (Com × State) -> (Com × State) -> Prop where
   | Assign : ∀ {x a s},
                SmallStep (x <~ a, s) (Skip, s [x := aval a s])
   | Seq1   : ∀ {c s},
                SmallStep ((Skip ;; c), s) (c, s)
   | Seq2   : ∀ {c1 c1' c2 s s'},
                SmallStep (c1, s) (c1', s') ->
                SmallStep ((c1 ;; c2) , s) ((c1' ;; c2), s')
   | IfTrue : ∀ {b c1 c2 s},
                bval b s == true ->
                SmallStep (IF b THEN c1 ELSE c2, s) (c1, s)
   | IfFalse : ∀ {b c1 c2 s},
                bval b s == false ->
                SmallStep (IF b THEN c1 ELSE c2, s) (c2, s)
   | While   : ∀ { b c s },
                SmallStep (Com.While b c, s) (Com.If b (c ;; (Com.While b c)) Skip, s)
```


## Many `SmallSteps`

We can now extend the *single* `SmallStep` relation to handle
arbitrarily many steps, simply by taking its **transitive closure**!

That is, recall the definition of `star r` as taking zero or more `r`-steps

```lean
inductive star {α : Type} (r: α -> α -> Prop) : α -> α -> Prop where
  | refl : ∀ {a : α}, star r a a
  | step : ∀ {x y z : α}, r x y -> star r y z -> star r x z
```

```lean
abbrev Steps := star SmallStep

notation:12 cs "~~>" cs' => SmallStep cs cs'
notation:12 cs "~~>*" cs' => Steps cs cs'
```


-- Lets revisit our old example with `c₀`

```lean
-- def chain (r : α -> α -> Prop) (x0 : α) (xs : List α) (xn : α) : Prop :=
--   match xs with
--   | [] => x0 = xn
--   | x::xs' => r x0 x /\ chain r x xs' xn


-- theorem chain_trans : ∀ {α : Type} {r : α -> α -> Prop } {x z : α},
--   (∃ ys, chain r x ys z) -> star r x z
--   := by
--   intros α r x z ch_xz; cases ch_xz; rename_i ys ch_xz
--   induction ys generalizing x z <;> simp_all [chain]
--   . case nil  =>
--     intros; constructor
--   . case cons =>
--     rename_i y ys ih
--     cases ch_xz
--     apply star.step
--     assumption
--     apply ih
--     assumption

-- theorem trans_chain : ∀ {α : Type} {r : α -> α -> Prop } {x z : α},
--   star r x z -> (∃ ys, chain r x ys z)
--   := by
--   intros α r x z r_x_z
--   induction r_x_z
--   . case refl =>
--     exists []
--   . case step =>
--     rename_i x y z xy yz ih
--     cases ih
--     rename_i ys _
--     exists (y::ys)

-- theorem witness_trans : ∀ {α : Type} {r : α -> α -> Prop } {x z : α},
--   (∃ ys, chain r x ys z) <-> star r x z
--   := by intros α r x z; constructor; apply chain_trans; apply trans_chain


-- example : ∃ c1 c2 c3 c4 c5 c6,
--   chain SmallStep (com₀, st₀) [c1, c2, c3, c4, c5, c6] (Skip, stₒ[ x := 10 ][ y := 11][ z := 13])
--   := by
--   apply Exists.intro
--   sorry

-- @[simp]
-- theorem assign_step : ∀ {x a c s},
--   ((((x <~ a) ;; c), s) ~~> (Skip;;c, s [x := aval a s]))
--   :=
--   by sorry


-- example : (com₀, st₀) ~~>* (Skip, stₒ[ x := 10 ][ y := 11][ z := 13]) := by
--    apply chain_trans
--    refine (Exists.intro [?c1, ?c2, ?c3, ?c4, ?c5, ?c6] ?horse)
--    rotate_right
--    and_intros
--    simp [chain, com₀]
--    apply assign_step

--    apply SmallStep.Assign
--    constructor
```


## `SmallStep` is Deterministic

Let us prove that the `~~>` relation is **deterministic**,
meaning, that each `Configuration` can only step to **at most**
one other `Configuration`.

In other words, if a configuration `cs ~~> cs1` and `cs ~~> cs2`
then `cs1` and `cs2` must be the same.

```lean
theorem smallstep_deterministic : ∀ {cs cs1 cs2},
  (cs ~~> cs1) -> (cs ~~> cs2) -> cs1 = cs2
  := by
  intros cs cs1 cs2 step1 step2
  induction step1 generalizing cs2 <;> cases step2 <;>
  sorry
```


## The Equivalence of `BigStep` and `SmallStep` Semantics

Next, let us prove that our `SmallStep` and `BigStep` definitions are **equivalent**.

How would we state the above as a theorem?



### Helper lemmas about `BigStep` Semantics

It will be handy to have some `@[simp]` lemmas to simplify facts about the `BigStep` semantics.
(Lean will automatically apply these everytime we say `simp` or `simp_all`.)


```lean
@[simp] theorem BigStep_skip_Iff : ∀ {s t},
  (⟨ Skip, s ⟩ ==> t) <-> (s = t) :=
  by
  intros s t; constructor
  . case mp  => intro h; cases h; simp_all []
  . case mpr => intros; simp_all []; constructor

@[simp] theorem BigStep_assign_Iff: ∀ {x a s t},
  (⟨ x <~ a, s ⟩ ==> t) <-> (t = (s[x := aval a s]))
  := by
  intros x a s t
  constructor
  . case mp  => intro h; cases h; simp_all []
  . case mpr => intros; simp_all []; constructor

@[simp] theorem BigStep_seq_Iff: ∀ {c1 c2 s t},
  (⟨ c1 ;; c2, s ⟩ ==> t) <-> (∃ s', (⟨ c1, s ⟩ ==> s') ∧ (⟨ c2, s' ⟩ ==> t)) := by
  intros c1 c2 s t
  apply Iff.intro
  . case mp => intros h; cases h; repeat constructor; repeat assumption
  . case mpr => intros h; cases h; rename_i _ h12; cases h12; constructor; repeat assumption
theorem steps_skip : ∀ {st cs},
  ((Skip, st) ~~>* cs) -> cs = (Skip, st)
  := by
  intros st cs steps
  cases steps
  . case refl => simp_all []
  . case step _ ih _ => cases ih
```


### `SmallStep` implies `BigStep`

Next, lets try to prove that
if using **many small steps** we have `(c, s) ~~>* (Skip, t)`
then, in a **single big step** we have `⟨ c, s ⟩ ==> t`.

The only way to do so will be an induction on the *sequence of small steps*.

```lean
theorem smallstep_implies_bigstep_stuck : ∀ {c s t},
  ((c, s) ~~>* (Skip, t)) -> (⟨ c, s ⟩ ==> t)  := by
  intros c s t steps
  generalize h1 : (c, s)    = c_s    at steps --- this is ANF / Nico's tip
  generalize h2 : (Skip, t) = skip_t at steps --- this is ANF / Nico's tip
  induction steps generalizing c s t
  . case refl =>
      cases h1
      cases h2
      constructor
  . case step cs cs1 skip_t step_head step_tail ih =>
      cases h1
      cases h2
      sorry
```


Yikes! We are stuck! We need some sort of *helper lemma* that will tell us
something about what happens after executing a *single* small step!

What should that lemma *say*?

**HINT** see where we got stuck in the above proof!


<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>


```lean
theorem step_case : ∀ {c c' s s' t},
  ((c, s) ~~> (c', s')) -> (⟨ c', s' ⟩ ==> t) -> (⟨ c, s ⟩ ==> t)
  := by
  intros c c' s s' t step1 bigstep
  generalize h1 : (c, s)   = cs at step1 --- this is ANF / Nico's tip
  generalize h2 : (c', s') = cs' at step1 --- this is ANF / Nico's tip
  induction step1 generalizing c c' s s' t <;> cases h1 <;> cases h2
  . case Assign x a s =>
      simp_all []
  . case Seq1 c s =>
      constructor
      constructor
      assumption
  . case Seq2 c1 c1' c2 s s' _hyp step_c1 =>
      cases bigstep
      rename_i st2 c1'_s'_st2' c2_st2
      constructor
      apply step_c1
      apply c1'_s'_st2'
      repeat simp_all []
  . case IfTrue b c1 c2 s hyp =>
      constructor
      simp_all []
      assumption
  . case IfFalse b c1 c2 s hyp =>
      apply BigStep.IfFalse
      simp_all []
      assumption
  . case While b c s =>
      generalize hyp : bval b s = bv
      cases bv
      -- bv = false
      cases bigstep
      repeat simp_all []
      apply BigStep.WhileFalse
      assumption
      -- bv = true
      cases bigstep
      simp_all []
      rename_i h_bv h_c_w
      cases h_c_w
      rename_i s' hh
      cases hh
      apply BigStep.WhileTrue
      repeat assumption
      simp_all []
```

We can now use the above lemma to complete the proof of the `smallstep_implies_bigstep` theorem.


```lean
theorem smallstep_implies_bigstep : ∀ {c s t}, ((c, s) ~~>* (Skip, t)) -> (⟨ c, s ⟩ ==> t)  := by
  intros c s t steps
  generalize h1 : (c, s)    = c_s    at steps --- this is ANF / Nico's tip
  generalize h2 : (Skip, t) = skip_t at steps --- this is ANF / Nico's tip
  induction steps generalizing c s t <;> cases h1 <;> cases h2
  . case refl =>
      constructor
  . case step _ step_head _ ih =>
      apply step_case
      apply step_head
      apply ih
      repeat simp_all []
```


### `BigStep` implies `SmallStep`

Next, lets try to prove the other direction that

IF in a **single big step** we have `⟨ c, s ⟩ ==> t`.
THEN using **many small steps** we have `(c, s) ~~>* (Skip, t)`.

Of course, this proof will be by induction on the `BigStep` derivation.


```lean
theorem bigstep_implies_smallstep' : ∀ {c s t},
  (⟨ c, s ⟩ ==> t) -> ((c, s) ~~>* (Skip, t))
  := by
  intros c s t bs
  induction bs
  . case Skip =>
    sorry
  . case Assign s x a =>
    sorry
  . case Seq c1 c2 s1 s2 s3 _ _ sc1 sc2 =>
    sorry
  . case IfTrue =>
    sorry
  . case IfFalse =>
    sorry
  . case WhileFalse b c st b_false =>
    sorry
  . case WhileTrue =>
    sorry
```



Uh oh, in the `Seq` case we get stuck because

- we have `⟨ c1, s ⟩ ==> s1`, which implies `(c1, s)  ~~>* (Skip, s1)` (by the IH)
- we have `⟨ c2, s1 ⟩ ==> t`, which implies `(c2, s1) ~~>* (Skip, t)`  (by the IH)

But we need to **join the `SmallStep` sequences** for `c1` and `c2` to get one for `c1;;c2`.

But how? We need some additional lemma, but what should that lemma *say*?

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>



```lean
theorem seq_steps : ∀ {c1 c1' c2 s s'},
  ((c1, s) ~~>* (c1', s')) ->
  ((c1;;c2, s) ~~>* (c1';;c2, s'))
  :=
  by
  intros c1 c1' c2 s s' steps_c1_c1'
  generalize h1 : (c1, s)   = c1s  at steps_c1_c1'
  generalize h2 : (c1', s') = c1s' at steps_c1_c1'
  induction steps_c1_c1' generalizing c1 c1' c2 s s'
  case refl =>
    rename_i a
    cases h1
    simp_all []
    apply star.refl
  case step  =>
    cases h1
    cases h2
    rename_i c1s'' step_c1_hd _ ih
    apply star.step
    constructor
    apply step_c1_hd
    apply ih
    simp_all []
    simp_all []
```



We can now use the above lemma to complete the proof...


```lean
---------------------------------------------------------------------------------

theorem bigstep_implies_smallstep : ∀ {c s t},
  (⟨ c, s ⟩ ==> t) -> ((c, s) ~~>* (Skip, t))
  := by
  intros c s t bs
  induction bs
  . case Skip =>
    constructor
  . case Assign s x a =>
    apply star.step; constructor; apply star.refl
  . case Seq c1 c2 st1 st2 st3 _ _ sc1 sc2 =>
      apply star_trans
      apply seq_steps
      apply sc1
      apply star.step
      apply SmallStep.Seq1
      apply sc2
  . case IfTrue =>
      constructor; apply SmallStep.IfTrue; simp_all []; assumption
  . case IfFalse =>
      constructor; apply SmallStep.IfFalse; simp_all []; assumption
  . case WhileFalse b c st b_false =>
      apply star.step; constructor; apply star_one; constructor; simp_all []
  . case WhileTrue =>
      rename_i b c st st1 st2 _ _ _ c_steps ih
      apply star.step; constructor
      apply star.step; constructor
      simp_all []
      apply star_trans
      apply seq_steps c_steps
      apply star.step; constructor
      assumption

----------------------------------------------------------------------------------------------
```


