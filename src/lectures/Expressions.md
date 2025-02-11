```lean
import Cse230wi25.States

set_option pp.fieldNotation false
set_option pp.proofs true


-- Arithmetic Expressions -------------------------------------

inductive Aexp where
  | num : Val -> Aexp
  | var : Vname -> Aexp
  | add : Aexp -> Aexp -> Aexp
  | sub : Aexp -> Aexp -> Aexp
  deriving Repr

open Aexp

class ToAexp (a : Type) where
  toAexp : a -> Aexp

instance : ToAexp Nat where
  toAexp := num

instance : ToAexp String where
  toAexp := var

instance : ToAexp Aexp where
  toAexp a := a

instance : OfNat Aexp (n: Nat) where
  ofNat := num n

instance : Add Aexp where
  add := fun a1 a2 => add a1 a2

-- instance [ToAexp a] [ToAexp b] : HAdd a b Aexp where
--   hAdd := fun s a => .Add (ToAexp.toAexp s) (ToAexp.toAexp a)

instance : HAdd String Aexp Aexp where
   hAdd := fun s a => add (var s) a

instance : HAdd String Nat Aexp where
   hAdd := fun s a => add (var s) (num a)

instance : HAdd String String Aexp where
   hAdd := fun s a => add (var s) (var a)

instance : HSub String Nat Aexp where
   hSub := fun s a => sub (var s) (num a)


def mkVar (s: String) (i : Nat) : Aexp := var (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs

@[simp]
def x := "x"

@[simp]
def y := "y"

@[simp]
def z := "z"

def aexp0 : Aexp := x#1 + y#1 + z#1 + 5

def aval (a: Aexp) (s: State) : Val :=
  match a with
  | num n => n
  | var x => s x
  | add a1 a2 => aval a1 s + aval a2 s
  | sub a1 a2 => aval a1 s - aval a2 s

-- initial state
def st0 : State := λ _ => 0
def aexp_5 := num 5
def aexp_x := var "x"
def aexp_x_plus_y := add (var "x") (var "y")
def aexp_2_plus_z_plus_3 := add (num 2) (add (var "z") (num 3))

-- Substitution -----------------------------------------------

def subst (x : Vname) (xa : Aexp) (a : Aexp) : Aexp :=
  match a with
  | num n => num n
  | var y => if x = y then xa else var y
  | add a1 a2 => add (subst x xa a1) (subst x xa a2)
  | sub a1 a2 => sub (subst x xa a1) (subst x xa a2)

example : subst "x" (num 3) (add (var "x") (var "y")) = add (num 3) (var "y") := rfl

theorem subst_aval : ∀ {x xa a}, aval (subst x xa a) s = aval a (s [x := aval xa s])
  := by
  intros x xa a
  induction a
  case num n => simp [subst, aval]
  case var y => simp [subst, aval]
                split
                case isTrue => simp [upd, *]
                case isFalse => simp [upd, *]; split <;> simp_all [aval]
  case add a1 a2 ih1 ih2 => simp_all [subst, aval]
  case sub a1 a2 ih1 ih2 => simp_all [subst, aval]


-- Boolean Expressions ---------------------------------------------

inductive Bexp where
  | Bc    : Bool -> Bexp
  | Bnot  : Bexp -> Bexp
  | Band  : Bexp -> Bexp -> Bexp
  | BLess : Aexp -> Aexp -> Bexp
  deriving Repr

open Bexp

class ToBexp (a : Type) where
  toBexp : a -> Bexp

@[simp]
instance : ToBexp Bool where
  toBexp := Bc

@[simp]
instance : ToBexp Bexp where
  toBexp (b) := b


def bval (b: Bexp) (st: State) : Bool :=
  match b with
  | Bc v        => v
  | Bnot b1     => ! bval b1 st
  | Band b1 b2  => bval b1 st && bval b2 st
  | BLess a1 a2 => aval a1 st < aval a2 st

def bsubst (x : Vname) (xa : Aexp) (b : Bexp) : Bexp :=
  match b with
  | Bc v        => Bc v
  | Bnot b'     => Bnot  (bsubst x xa b')
  | Band  b1 b2 => Band  (bsubst x xa b1) (bsubst x xa b2)
  | BLess a1 a2 => BLess (subst x xa a1) (subst x xa a2)

theorem subst_bval : ∀ {x xa b}, bval (bsubst x xa b) s = bval b (s [x := aval xa s]) := by
  intros x xa b
  induction b
  case Bc v       => simp_all [bsubst, bval]
  case Bnot b' ih => simp_all [bsubst, bval, ih]
  case Band b1 b2 ih1 ih2 => simp_all [bsubst, bval, ih1, ih2]
  case BLess a1 a2 => simp_all [bsubst, bval, subst_aval]
```

