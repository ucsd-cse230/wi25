set_option pp.fieldNotation false

/- @@@
# Datatypes and Recursion

This material is based on

- Chapter 2 of [Concrete Semantics](http://www.concrete-semantics.org/)
- Induction Exercises by [James Wilcox](https://jamesrwilcox.com/InductionExercises.html)

@@@-/

namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
  deriving Repr

open Nat

def add (n m : Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)

/- @@@
## Trick 1: Helper Lemmas
@@@ -/


/- @@@
### Helper Lemmas: Example `add_comm`
@@@ -/

theorem add_zero: ∀ (n : Nat), add n zero = n := by
  intros n
  induction n
  . case zero => simp [add]
  . case succ => simp [add, *]

theorem add_succ: ∀ (n m : Nat), add n (succ m) = succ (add n m) := by
  intros n m
  induction n
  . case zero => simp [add]
  . case succ => simp [add, *]

theorem add_comm : ∀ (n m: Nat), add n m = add m n := by
  intros n m
  induction n
  . case zero => simp [add, add_zero]
  . case succ n' ih => simp [add, ih, add_succ]

end MyNat

/- @@@
### Helper Lemmas: Example `rev_rev`
@@@ -/

open List

/-@@@
**Appending lists**
@@@-/

def app {α : Type} (xs ys: List α) : List α :=
  match xs with
  | [] => ys
  | x::xs' => x :: app xs' ys

example : app [0,1,2] [3,4,5] = [0,1,2,3,4,5] := rfl

/-@@@
**Reversing lists**
@@@-/

def rev {α : Type} (xs: List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => app (rev xs') [x]

example : rev [0,1,2,3] = [3,2,1,0] := rfl

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

theorem rev_app : ∀ {α : Type} (xs ys: List α), rev (app xs ys) = app (rev ys) (rev xs) := by
  intro α xs ys
  induction xs
  case nil => simp [app, rev, app_nil]
  case cons x xs' ih => simp [app, rev, ih, app_assoc]

theorem rev_rev : ∀ {α : Type} (xs: List α), rev (rev xs) = xs := by
  intro α xs
  induction xs
  case nil  => rfl
  case cons => simp [rev, rev_app, app, *]


/- @@@
## Trick 2: Generalizing
@@@ -/

open MyNat.Nat

def itadd (n m: MyNat.Nat) : MyNat.Nat :=
  match n with
  | zero => m
  | succ n' => itadd n' (succ m)

theorem itadd_eq : ∀ (n m: MyNat.Nat), itadd n m = MyNat.add n m := by
  intros n m
  induction n generalizing m
  case zero => simp [MyNat.add, itadd]
  case succ => simp [MyNat.add, MyNat.add_succ, itadd, *]

open List

def itrev {α : Type} (xs ys: List α) : List α :=
  match xs with
  | [] => ys
  | x ::xs' => itrev xs' (x :: ys)

theorem itrev_app : ∀ {α : Type} (xs ys: List α), itrev xs ys = app (rev xs) ys := by
  intros α xs ys
  induction xs generalizing ys
  case nil => rfl
  case cons x xs' ih => simp [itrev, ih, rev, app_assoc, app]

theorem itrev_eq_rev : ∀ {α : Type} (xs: List α), itrev xs [] = rev xs := by
  intros α xs
  simp [itrev_app, app_nil]


/- @@@
## Trick 3: Functional Induction

Based on [Joachim Breitner's notes on Functional Induction](https://lean-lang.org/blog/2024-5-17-functional-induction/)

@@@ -/

def len (xs: List α) : Nat :=
  match xs with
  | [] => 0
  | _::xs' => 1 + len xs'

def alt (xs ys : List α) : List α :=
  match xs, ys with
  | [], ys => ys
  | xs, [] => xs
  | x::xs, y::ys => x :: y :: alt xs ys

#eval alt [1,2,3,4] [10,20,30]

theorem alt_length : ∀ {α : Type} (xs ys : List α), len (alt xs ys) = len xs + len ys := by
  intros α xs ys
  induction xs, ys using alt.induct
  . case case1 => simp [alt, len]
  . case case2 => simp [alt, len]
  . case case3 => simp_arith [alt, len, *]
