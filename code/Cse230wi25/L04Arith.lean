set_option pp.fieldNotation false

/- @@@

# Expressions

This material is based on

- Chapter 3 of [Concrete Semantics](http://www.concrete-semantics.org/)

@@@-/

/- @@@
## Arithmetic Expressions
@@@ -/

abbrev Val := Nat
abbrev Vname := String

inductive Aexp where
| num : Val -> Aexp
| var : Vname -> Aexp
| add : Aexp -> Aexp -> Aexp
deriving Repr

open Aexp

def aexp_5 := num 5
def aexp_x := var "x"
def aexp_x_plus_y := add (var "x") (var "y")
def aexp_2_plus_z_plus_3 := add (num 2) (add (var "z") (num 3))

/- @@@
## States
@@@ -/

abbrev State := Vname -> Val

-- initial state
def st0 : State := λ _ => 0

-- update state
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y

/- @@@
## Evaluation
@@@ -/

def aval (a: Aexp) (s: State) : Val :=
  match a with
  | num n => n
  | var x => s x
  | add a1 a2 => aval a1 s + aval a2 s

notation:10 st " [ " x " := " v " ] " => upd st x v

def st1 := st0 ["x" := 2] [ "y" := 10 ] [ "z" := 100 ]

example : aval aexp_5 st0 = 5 := rfl
example : aval aexp_x st0 = 0 := rfl

example : aval aexp_x_plus_y st1 = 12 := rfl
example : aval aexp_2_plus_z_plus_3 st1 = 105 := rfl

/- @@@
## Constant Folding

Compilers often want to "simplify" expressions by performing,
at compile time, various operations on constants.

For example, we may want to simplify an expression

```lean
add (var "x") (add (num 3) (num 1))
```

to just

```lean
add (var "x") (num 4)
```

We can implement this idea in a little recursive funciton `asimp_const`
that does this form of **constant folding** in a bottom-up manner

@@@ -/


def asimp_const (a: Aexp) : Aexp :=
  match a with
  | num n => num n
  | var x => var x
  | add a1 a2 => match asimp_const a1, asimp_const a2 with
                 | num n1, num n2 => num (n1 + n2)
                 | a1', a2' => add a1' a2'

/- @@@
## Equivalence of Constant Folding

Lets prove that `asimp_const` does not **change the meaning** of the expression `a`.
@@@ -/

theorem aval_asimp_const : ∀ a s, aval a s = aval (asimp_const a) s  := by
  sorry

/- @@@
## TACTIC: `simp_all` to simplify _hypotheses_

Lets flip the order of the equality.
@@@ -/


-- REWRITING hypotheses: simp_all
theorem aval_asimp_const' : ∀ a s, aval (asimp_const a) s  = aval a s := by
  sorry

/- @@@
Oh no! The exact same proof does not work! `lean` is stuck at the goal

```lean
s : State
a✝¹ a✝ : Aexp
n1✝ n2✝ : Val
x✝¹ : asimp_const a✝ = num n2✝
x✝ : asimp_const a✝¹ = num n1✝
ih2✝ : aval (asimp_const a✝¹) s = aval a✝¹ s
ih1✝ : aval (asimp_const a✝) s = aval a✝ s

⊢ n1✝ + n2✝ = aval a✝¹ s + aval a✝ s
```

Here, we **have the hypotheses** of the IH,

- `ih2✝ : aval (asimp_const a✝¹) s = aval a✝¹ s`
- `ih1✝ : aval (asimp_const a✝) s = aval a✝ s`

and separately we know that

- `... : asimp_const a✝ = num n2✝`
- `... : asimp_const a✝¹ = num n1✝`

So what we want is to apply the above "knowledge" to rewrite the `ih1✝` and `ih2✝`, which is
achieved by the tactic `simp_all`; which then makes the proof go through.


## Extended Folding with a Smart Constructor

Lets extend the constant folding so that additions-by-zero are dropped,
i.e. `add (num 0) a` or `add a (num 0)` just become `a`.

A clean way to do so is by writing a **smart constructor** `plus` which handles
both the num-num-addition and the zero-addition cases as
@@@ -/

def plus (a1 a2: Aexp) : Aexp :=
  match a1, a2 with
  | num n1, num n2 => num (n1 + n2)
  | num n , a      => if n = 0 then a else add (num n) a
  | a, num n       => if n = 0 then a else add a (num n)
  | _, _           => add a1 a2

/- @@@
We can now write a general simplifier `asimp` that recursively
traverses the `Aexp` and invokes `plus` at each `add`
@@@ -/

def asimp (a: Aexp) : Aexp :=
  match a with
  | num n => num n
  | var x => var x
  | add a1 a2 => plus (asimp a1) (asimp a2)

/- @@@

Lets try to prove that `asimp` does not change the meaning of an expression.

Oof. The "direct" proof-by-induction is stuck. Can you think of a suitable "helper lemma"?
@@@ -/


theorem aval_asimp : ∀ a s, aval a s = aval (asimp a) s := by
/- @@@ BEGIN:SORRY @@@ -/
  intros a s
  induction a <;> simp [asimp, aval, *]
  sorry


/- @@@
## Boolean Expressions

Lets define a datatype for boolean expressions
@@@ -/


inductive Bexp where
  | bbool : Bool -> Bexp
  | bnot  : Bexp  -> Bexp
  | band  : Bexp  -> Bexp -> Bexp
  | bless : Aexp  -> Aexp -> Bexp
  deriving Repr

open Bexp

def bval (b: Bexp) (s: State) : Bool :=
  match b with
  | bbool v => v
  | bnot b' => !bval b' s
  | band b1 b2 => bval b1 s && bval b2 s
  | bless a1 a2 => aval a1 s < aval a2 s

def smart_and (b1 b2: Bexp) : Bexp :=
  match b1, b2 with
  | bbool true, _  => b2
  | _, bbool true  => b1
  | bbool false, _ => bbool false
  | _, bbool false => bbool false
  | _, _           => band b1 b2

def smart_not (b: Bexp) : Bexp :=
  match b with
  | bbool true  => bbool false
  | bbool false => bbool true
  | _           => bnot b

def smart_less (a1 a2: Aexp) : Bexp :=
  match a1, a2 with
  | num n1, num n2 => bbool (n1 < n2)
  | _, _           => bless a1 a2

def bsimp (b: Bexp) : Bexp :=
  match b with
  | bbool v    => bbool v
  | bnot b     => smart_not (bsimp b)
  | band b1 b2 => smart_and (bsimp b1) (bsimp b2)
  | bless a1 a2 => smart_less (asimp a1) (asimp a2)

theorem smart_not_eq : ∀ b s, bval (smart_not b) s = bval (bnot b) s := by
  intros b s
  cases b
  . case bbool v => cases v <;> rfl
  . case bnot    => rfl
  . case band    => rfl
  . case bless   => rfl


theorem smart_and_eq : ∀ b1 b2 s, bval (smart_and b1 b2) s = bval (band b1 b2) s := by sorry
theorem smart_less_eq : ∀ a1 a2 s, bval (smart_less a1 a2) s = bval (bless a1 a2) s := by sorry

theorem bval_bsimp : ∀ b s, bval b s = bval (bsimp b) s := by
  intros b s
  sorry

