```lean
set_option pp.fieldNotation false
```

# Datatypes and Recursion

This material is based on

- Chapter 2 of [Concrete Semantics](http://www.concrete-semantics.org/)
- Induction Exercises by [James Wilcox](https://jamesrwilcox.com/InductionExercises.html)


```lean
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
```

## Trick 1: Helper Lemmas


### Helper Lemmas: Example `add_comm`


```lean
theorem add_zero : ∀ (m : Nat),
  add m zero = m := by
  intros m
  induction m
  . case zero =>
    rfl
  . case succ m' ih =>
    simp [add, ih]

theorem add_succ : ∀ (m n : Nat),
  add m (succ n) = succ (add m n) := by
  intros m n
  induction m
  . case zero => rfl
  . case succ m' ih =>
    simp [add, *]

theorem add_comm : ∀ (n m: Nat),
  add n m = add m n := by
  intros n m
  induction n
  . case zero =>
    simp [add, add_zero]
  . case succ n' ih =>
    simp [add, add_succ, *]







end MyNat
```

### Helper Lemmas: Example `rev_rev`

```lean
open List
```

**Appending lists**

```lean
def app {α : Type} (xs ys: List α) : List α :=
  match xs with
  | [] => ys
  | x::xs' => x :: app xs' ys

example : app [0,1,2] [3,4,5] = [0,1,2,3,4,5] := rfl
```

**Reversing lists**

```lean
def rev {α : Type} (xs: List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => app (rev xs') [x]

example : rev [0,1,2,3] = [3,2,1,0] := rfl

------- CUT -----

theorem rev_rev : ∀ {α : Type} (xs: List α),
  rev (rev xs) = xs := by
  sorry
```


## Trick 2: Generalizing

```lean
open MyNat.Nat

def itadd (n m: MyNat.Nat) : MyNat.Nat :=
  match n with
  | zero => m
  | succ n' => itadd n' (succ m)

theorem itadd_eq : ∀ (n m: MyNat.Nat), itadd n m = MyNat.add n m := by
  sorry

open List

def itrev {α : Type} (xs ys: List α) : List α :=
  match xs with
  | [] => ys
  | x ::xs' => itrev xs' (x :: ys)

theorem itrev_eq_rev : ∀ {α : Type} (xs: List α), itrev xs [] = rev xs := by
  sorry
```


## Trick 3: Functional Induction

Based on [Joachim Breitner's notes on Functional Induction](https://lean-lang.org/blog/2024-5-17-functional-induction/)


```lean
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
  sorry
```

