import Cse230wi25.L04Arith

set_option pp.fieldNotation false
set_option pp.proofs true

open Aexp
open Bexp

/- @@@

## Lean Tip: Overloading Operators

Some convenient ways to "write" `Aexp` in lean by overloading the `+` operator.

@@@ -/

class ToAexp (a : Type) where
  toAexp : a -> Aexp

instance : ToAexp Nat where
  toAexp := num

instance : ToAexp String where
  toAexp := var

instance : OfNat Aexp (n: Nat) where
  ofNat := num n

instance : Add Aexp where
  add := fun a1 a2 => add a1 a2

instance : HAdd String Aexp Aexp where
  hAdd := fun s a => add (var s) a

instance : HAdd String Nat Aexp where
  hAdd := fun s a => add (var s) (num a)

def mkVar (s: String) (i : Nat) : Aexp := var (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs

def x := "x"
def y := "y"
def z := "z"

def aexp0 : Aexp := x#1 + y#1 + z#1 + 5

#eval aexp0

/- @@@
## An Imperative Language: `Com`
@@@ -/


inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  deriving Repr

open Com

/- @@@
More notation tricks to make it easier to write `Com` programs.
@@@ -/


infix:10 "<<"  => fun x y => bless (ToAexp.toAexp x) (ToAexp.toAexp y)
infix:10 "<~"  => Com.Assign
infixr:8 ";;"  => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

def com0 := x <~ y + 1
def com1 := y <~ 2
def com2 := com0 ;; com1
def com3 := x <~ y + 1 ;; y <~ x + 2
def com4 := Skip ;; Skip ;; Skip ;; Skip
def com5 := IF 10 << x THEN x <~ 1 ELSE y <~ 2
def com6 := WHILE x << 5 DO x <~ x + 1 END

def st_x_10_y_20 := st0 [x := 10 ] [ y := 20]

#eval com3
#eval com4

/- @@@
## Big Step Semantics for `Com`



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
<br>

@@@ -/


inductive BigStep : Com -> State -> State -> Prop where
  | Skip   : ∀ {st},
                BigStep Skip st st
  | Assign : ∀ {st a n},
                BigStep (Assign a n) st (st [a := aval n st])
  | Seq    : ∀ {c1 c2 st1 st2 st3},
                BigStep c1 st1 st2 -> BigStep c2 st2 st3 ->
                BigStep (Seq c1 c2) st1 st3
  | IfTrue : ∀ {b c1 c2 st st'},
                bval b st = true -> BigStep c1 st st' ->
                BigStep (If b c1 c2) st st'
  | IfFalse : ∀ {b c1 c2 st st'},
                bval b st = false -> BigStep c2 st st' ->
                BigStep (If b c1 c2) st st'
  | WhileFalse : ∀ {b c st},
                bval b st = false ->
                BigStep (While b c) st st
  | WhileTrue : ∀ {b c st st' st''},
                bval b st = true -> BigStep c st st' -> BigStep (While b c) st' st'' ->
                BigStep (While b c) st st''

notation:12 "⟨" c "," s "⟩" "==>" t  => BigStep c s t

/- @@@

### Big Step Evaluation: Examples

We say that `c : Com` started in `s: State` big-steps to `t : State`
whenever we have the proposition `⟨ c, s ⟩ ==> t`. This proposition
captures the intuition that when you "run" the command `c` from a
state `s`, the execution terminates in the state `t`.

Let's try some examples of "running" `Com` programs using the big step semantics.

@@@ -/

example : ⟨ (x <~ 5 ;; y <~ var x) , st0 ⟩ ==> st0 [x := 5] [y := 5] := by
  apply BigStep.Seq
  apply BigStep.Assign
  apply BigStep.Assign

example : ⟨ (x <~ 5 ;; y <~ var x) , st0 ⟩ ==> st0 [x := 5] [y := 5] := by
  repeat constructor

example : ⟨ (x <~ 5 ;; y <~ x + 1) , st0 ⟩ ==> st0 [x := 5] [y := 6] := by
  repeat constructor

/- @@@

### EXERCISE: Using Big Step Evaluation

Lets see how we can use big-step semantics to precisely state and verify some
intuitive facts about programs.

Suppose we have a command `c` that *does not assign to* a variable `x`.
Now, suppose that when we run `c` from a state `s` we finish at state `t`.

What do you think is the relationship between the value of `x` at `s` and `t`?

Can you try to formalize the above "english" as a precise theorem? (Ex 7.1 from NK)

@@@ -/

/- @@@ START: CUT @@@ -/
def assigned(c: Com) : Vname -> Bool :=
  match c with
  | Com.Assign x _ => fun y => x == y
  | Com.Seq c1 c2  => fun y => assigned c1 y || assigned c2 y
  | Com.If _ c1 c2 => fun y => assigned c1 y || assigned c2 y
  | Com.While _ c  => fun y => assigned c y
  | Com.Skip       => fun _ => false

theorem ex_unchanged : (⟨ c, s ⟩ ==> t) -> (assigned c x == false) -> s x = t x := by
  intros cst asg
  induction cst <;> simp_all [assigned]
  . case Assign st a n =>
    simp_all [upd]
    split <;> simp_all []
/- @@@ END: CUT @@@ -/


/- @@@

## Equivalence of Commands

We say that two commands `c1` and `c2` are **equivalent**
if `c1` started in `s` big-steps to `t` **iff** `c2`
started in `s` also big-steps to `t`.

We can formalize this idea as a definition.

**NOTE:** The `≃` symbol can be typed as `\` + `equiv`.

@@@ -/

def equiv_com (c1 c2 : Com) := ∀ {st st' : State}, ( ⟨ c1, st ⟩ ==> st') ↔ ( ⟨ c2, st ⟩ ==> st' )

infix:50 "≃"  => equiv_com

/- @@@
Lets prove that a sequence of three commands `c1,c2,c3` does the same thing,
no matter where you put the `;;` i.e. `(c1;;c2);;c3` is equivalant to `c1;;(c2;;c3)`


@@@ -/

theorem seq_assoc : ∀ {c1 c2 c3}, (c1 ;; (c2 ;; c3)) ≃ ((c1 ;; c2) ;; c3) := by
/- @@@ START:SORRY @@@ -/
   intros c1 c2 c3 st st
   constructor    -- This breaks the `≃` into tw
   . case mp =>
     intros tx1_23
     cases tx1_23
     rename_i tx23
     cases tx23
     repeat (constructor; repeat assumption)
   . case mpr =>
     intros tx12_3
     cases tx12_3
     rename_i tx1_2 _
     cases tx1_2
     repeat (constructor; repeat assumption)
/- @@@ END:SORRY @@@ -/

/- @@@

**NOTE:** how the first `constructor` splits the proof into two subgoals.

```lean
-- case mp
c1 c2 c3 : Com
st st' : State
⊢ (⟨c1;;c2;;c3,st⟩ ==> st') → (⟨(c1;;c2);;c3,st⟩ ==> st')

-- case mpr
c1 c2 c3 : Com
st st' : State
⊢ (⟨(c1;;c2);;c3,st⟩ ==> st') → (⟨c1;;c2;;c3,st⟩ ==> st')
```

Because in general, to prove that `P ↔ Q` we need to prove two things,

* `case mp` which corresponds to `P → Q` (*assuming `P`, prove `Q`*) and
* `case mpr` which corresponds to `Q -> P` (*assuming `Q`, prove `P`*).

Lets do a few more such equivalences.
@@@ -/

theorem skip_skip : ∀ {c: Com}, (Skip ;; c) ≃ c := by
/- @@@ START:SORRY @@@ -/
  intros c st st'
  constructor
  . case mp =>
    intros tx_skip_c
    cases tx_skip_c
    rename_i _ tx_skip tx_c
    cases tx_skip
    assumption
  . case mpr =>
    intros tx_c
    constructor
    constructor
    assumption
/- @@@ END:SORRY @@@ -/

/- @@@

### Lean Tip: Case Splitting on Assumptions

Lets try to prove that `IF b then c else c` is equivalent to `c`.

@@@ -/

theorem if_c_c_stuck : ∀ { b c }, (IF b THEN c ELSE c) ≃ c := by
   intros b c s s'
   constructor
   case mp =>
    intros tx_if; cases tx_if <;> assumption
   case mpr =>
    intros tx_c
    sorry -- STUCK! we don't know if `bval b s` is `true` or `false`!

/- @@@

Yikes! In the `mpr` case we are *stuck* because we don't know if the `bval b s`
is `true` or `false` and so we don't know whether to take the `THEN` or `ELSE`
branch! Of course, in this case, it *does not matter* which branch we take: either
way we are going to run `c` so lets just tell `lean` to **case split**
on the value of `bval b s` by

1. **adding a new hypothesis** `hb : bval b s` and
2. **case splitting** on the value of `cases hb : bval b s`

@@@ -/

theorem if_c_c : ∀ { b c }, (IF b THEN c ELSE c) ≃ c := by
   intros b c s s'
   constructor
   case mp =>
    intros tx_if; cases tx_if <;> assumption
   case mpr =>
    intros tx_c
    cases hb : bval b s
    -- aha, split cases on the `hb : bval b s`
    . case false =>
      -- we have: hb: bval b s = false
      apply BigStep.IfFalse <;> assumption
    . case true =>
      -- we have: hb: bval b s = true
      apply BigStep.IfTrue  <;> assumption

/- @@@
**Exercise:** Complete the proof of the below.
@@@ -/

theorem unfold_while : ∀ {b c},
  (WHILE b DO c END) ≃ ((IF b THEN c ELSE Skip) ;; (WHILE b DO c END)) :=
  by
/- @@@ START:SORRY @@@ -/
  intros b c s s'
  constructor
  . case mp =>
    intros tx_w; cases tx_w
    . case WhileFalse =>
      constructor
      . case a => apply BigStep.IfFalse <;> solve_by_elim
      . case a => solve_by_elim
    . case WhileTrue =>
      constructor <;> solve_by_elim
  . case mpr =>
    intros tx_if_w
    cases tx_if_w
    rename_i _ tx_if _
    cases tx_if
    . case Seq.IfTrue => solve_by_elim
    . case Seq.IfFalse => rename_i tx_skip; cases tx_skip; solve_by_elim
/- @@@ END:SORRY @@@ -/

/- @@@

### `equiv_com` is an equivalence relation

It is easy to prove that `≃` is an **equivalence relation**, that is,
it is **reflexive**, **symmetric** and **transitive**.

@@@ -/

theorem equiv_refl : ∀ {c}, c ≃ c := by
  simp_all [equiv_com]

theorem equiv_symm : ∀ {c c'}, c ≃ c' -> c' ≃ c := by
  simp_all [equiv_com]

theorem equiv_trans : ∀ {c1 c2 c3}, c1 ≃ c2 -> c2 ≃ c3 -> c1 ≃ c3 := by
  simp_all [equiv_com]

/- @@@
**Exercise:** Complete the proof of the below; you may need a helper lemma.
(Exercise 7.6 from [Nipkow and Klein](http://www.concrete-semantics.org/)).
@@@ -/

theorem while_cong_helper : ∀ {b c c' s t},
  (⟨ WHILE b DO c END , s ⟩ ==> t) ->
  c ≃ c' ->
  (⟨ WHILE b DO c' END, s ⟩ ==> t) := by
/- @@@ START:SORRY @@@ -/
   intros b c c' s t tx_wc c_eq_c'
   generalize h : (WHILE b DO c END) = x at tx_wc -- this is ANF / Nico's tip
   induction tx_wc <;> simp_all []
   . case WhileFalse =>
      constructor <;> try assumption
   . case WhileTrue =>
      constructor <;> try assumption
      simp_all [equiv_com]
/- @@@ END:SORRY @@@ -/

theorem while_cong : ∀ {b c c'},
  c ≃ c' ->
  (WHILE b DO c END) ≃ (WHILE b DO c' END) := by
  intros b c c' c_eq_c'
  simp_all [equiv_com]
  intros st st'
  apply Iff.intro
  . case mp =>
      intros wc
      apply while_cong_helper
      assumption
      assumption
  . case mpr =>
      intros wc
      apply while_cong_helper
      assumption
      apply equiv_symm
      assumption



/- @@@

## Verifying an Optimization

Consider the following code

```
x <~ a ;; y <~ a
```

It seems a bit *redundant* to compute the `a` again, when we have just assigned it to `x`, right?

Instead, we should be able to just replace the above with

```
x <~ a ;; y <~ x
```

That is, just "copy" the value we computed and saved in `x`.

Right?

Lets see if we can formalize this as an *equivalence* ...

@@@ -/

def reads (a: Aexp) (x: Vname) : Bool :=
  match a with
  | var y     => x = y
  | num _     => false
  | add a1 a2 => reads a1 x || reads a2 x

theorem unmodified_assign: ∀ {x a n s}, reads a x = false -> (aval a (s [x := n]) = aval a s) := by
  intros x a n s not_reads_x
  induction a <;> simp_all [aval, reads]
  . case var => simp_all [upd]; intros; simp_all []

@[simp]
theorem assign_step : ∀ {x a s t}, (⟨ x <~ a, s ⟩ ==> t) <-> (t = (s [x := (aval a s)])) := by
  intros x a s t
  apply Iff.intro
  .case mp => intros xs; cases xs ; trivial
  .case mpr => intros; simp_all [] ; apply BigStep.Assign

theorem redundant_assign : ∀ {x y a}, reads a x = false -> (x <~ a ;; y <~ a) ≃ (x <~ a ;; y <~ var x) := by
  simp_all [equiv_com]
  intros x y a not_reads s t
  generalize ff : aval a s = n
  have aa : aval a (s [x := n ]) = aval a s  := by
    apply unmodified_assign; assumption
  constructor
  . case mp =>
    intros xaya; cases xaya; rename_i s' xa ya
    cases xa; cases ya
    constructor
    constructor
    simp [aval]
    simp_all [upd]
  . case mpr =>
    intros xayx; cases xayx; rename_i s' xa yx
    cases xa; cases yx
    constructor
    constructor
    simp [aval]
    simp_all [upd]



/- @@@

### BigStep Semantics are Deterministic

Finally, we want to design languages that are **deterministic** which means,
that if you *start* running a command `c` from some state `s` then there is *at most*
one state `t` that it can *finish* in. (It would be rather strange if we started in the
same state and *sometimes* the program finished with `x = 10` and at other times `x = 20`).

**EXERCISE:** Can you think of some examples where programs are **non-deterministic** ?

How can we *specify* that our big step semantics for `Com` are indeed deterministic?


<br>
<br>
<br>
<br>
<br>
<br>
<br>

And now, how can we *prove* it?

<br>
<br>
<br>
<br>
<br>
<br>
<br>
<br>

**HINT:**

1. Recall `induction ... generalizing`
2. Recall that you can "add" facts to your hypotheses using `have`

@@@ -/

theorem bigstep_deterministic : ∀ {c s t1 t2},
  (⟨ c, s ⟩ ==> t1) -> (⟨ c, s ⟩ ==> t2) -> t1 = t2 := by
  intros c s t1 t2 tx_s_to_t1 tx_s_to_t2
  induction tx_s_to_t1 generalizing t2
  . case Skip =>
    cases tx_s_to_t2
    rfl
  . case Assign =>
    cases tx_s_to_t2
    rfl
  . case Seq =>
    rename_i c1 c2 s0 s1 s2 _ _ ih1 ih2
    cases tx_s_to_t2
    rename_i s1' tx_c1_s0_s1' tx_c2_s1'_t2
    apply ih2
    have fact1 := ih1 tx_c1_s0_s1'
    simp_all []
  . case IfTrue =>
    cases tx_s_to_t2 <;> simp_all []
    rename_i ih _ _
    apply ih
    assumption
  . case IfFalse =>
    cases tx_s_to_t2 <;> simp_all []
    rename_i ih _ _
    apply ih
    assumption
  . case WhileFalse =>
    cases tx_s_to_t2 <;> simp_all []
  . case WhileTrue =>
    cases tx_s_to_t2 <;> simp_all []
    rename_i _ _ ih_c ih_w _ _ tx_c2 tx_w2
    apply ih_w
    have fact1 := ih_c tx_c2
    simp_all []
