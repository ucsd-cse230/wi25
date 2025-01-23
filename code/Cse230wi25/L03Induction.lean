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

### Example `add_comm`

Let's try to prove that `add` is commutative; that is, that the order of arguments does not matter.

If we plunge into trying a direct proof-by-induction, we get stuck at two places.

1. What is the value of `add m zero` ?
2. What is the value of `add m (succ n)` ?

It will be convenient to have **helper lemmas** that tell us that

1. `∀ m, add m zero = m`
2. `∀ n m, add n (succ m) = succ (add n m)`

@@@ -/


theorem add_comm : ∀ (n m: Nat), add n m = add m n := by
  intros n m
  induction n
  sorry

end MyNat

open List

/- @@@
### Example `rev_rev`

Lets look at another example where we will need helper lemmas.

@@@ -/


/-@@@
**Appending lists**
@@@-/

def app {α : Type} (xs ys: List α) : List α :=
  match xs with
  | [] => ys
  | x::xs' => x :: app xs' ys

/-
app [] [3,4,5] = [3,4,5]

app (2::[]) [3,4,5] = [3,4,5]
==>
2 :: [3,4,5]
==>
[2,3,4,5]
-/

example : app [] [3,4,5] = [3,4,5] := rfl
example : app [0,1,2] [3,4,5] = [0,1,2,3,4,5] := rfl

/-@@@
**Reversing lists**
@@@-/

def rev {α : Type} (xs: List α) : List α :=
 match xs with
  | [] => []
  | x :: xs' => app (rev xs') [x]

example : rev [] = ([] : List Int) := rfl
example : rev [3] = [3] := rfl
example : rev [2,3] = [3,2] := rfl
example : rev [0,1,2,3] = [3,2,1,0] := rfl
example : rev (rev [0,1,2,3]) = [0,1,2,3] := rfl

/- @@@
rev [0,1,2,3]
=>
rev (0 :: [1,2,3])
=>
app (rev [1,2,3]) [0]
=>
app [3,2,1] [0]
=>
[3,2,1,0]


Now, lets _prove_ that the above was not a fluke:
if you reverse a list *twice* then you get back
the original list.
@@@ -/

theorem rev_app : ∀ {α : Type} (xs ys : List α),
  rev (app xs ys) = app (rev ys) (rev xs) := by
    sorry

/-
rev (app xs ys) == app (rev ys) (rev xs)
rev (app [x1,x2,x3,...xn] [y1...ym])
== rev [x1...xn, y1...ym]
== [ym ... y1, xn ... x1]
== app [ym ... y1] [xn ... x1]
== app (rev ys) (rev xs)

-- |- rev (app (rev xs') [x]) = x :: xs'
      ==>
      app (rev [x]) (rev (rev xs'))
-/

theorem rev_rev : ∀ {α : Type} (xs: List α), rev (rev xs) = xs := by
  intros α xs
  induction xs
  . case nil =>
    rfl
  . case cons x xs' ih =>
    simp [rev, rev_app, app, ih]


/- @@@
Yikes. We're stuck again. What helper lemmas could we need?









## Trick 2: Generalizing the Variables

Consider the below variant of `add`.

How is it different than the original?
@@@ -/

open MyNat.Nat

def itadd (n m: MyNat.Nat) : MyNat.Nat :=
  match n with
  | zero => m
  | succ n' => itadd n' (succ m)

/-
  itadd (s s s z) (s s s s s z)
  =>
  itadd (s s z) (s s s s s s z)
  =>
  itadd (s z) (s s s s s s s z)
  =>
  itadd (z) (s s s s s s s s z)
  =>
  (s s s s s s s s z)
-/


example : itadd (succ (succ zero)) (succ zero) = succ (succ (succ zero)):= by rfl

/- @@@
Lets try to prove that `itadd` is equivalent to `add`.

add n' (succ m) == succ (add n' m)
@@@ -/

theorem add_succ : ∀ (n m), MyNat.add n (succ m) = succ (MyNat.add n m) := by
 sorry

theorem itadd_eq : ∀ (n m), itadd n m = MyNat.add n m := by
  intros n
  induction n
  . case zero => simp [itadd, MyNat.add]
  . case succ n' ih =>
    simp [MyNat.add, itadd, add_succ, ih]

/- @@@
Ugh! Why does the proof fail???

We are left with the goal

```lean
m n' : MyNat.Nat
ih : itadd n' m = MyNat.add n' m
⊢ itadd n' (succ m) = succ (MyNat.add n' m)
```

**IH is too weak**

In the goal above, the `ih` *only* talks about `itadd n m` but *says nothing*
about `itadd n (succ m)`. In fact, the IH should be true **for all** values of `m`
as we **do not really care** about `m` in this theorem. That is, we want to tell
`lean` that the `ih` should be

```lean
m n' : MyNat.Nat
ih : ∀ m, itadd n' m = MyNat.add n' m
⊢ itadd n' (succ m) = succ (MyNat.add n' m)
```

**Generalizing**
We can do so, by using the `induction n generalizing m` which tells `lean` that

- we are doing induction on `n` and
- we *don't care* about the value of `m`

Now, go and see what the `ih` looks like in the `case succ ...`

This time we can **actually use** the `ih` and so the proof works.
@@@ -/

theorem add_succ : ∀ (n m), MyNat.add n (succ m) = succ (MyNat.add n m) := by
 sorry

theorem itadd_eq' : ∀ (n m: MyNat.Nat), itadd n m = MyNat.add n m := by
  intros n m
  induction n generalizing m
  case zero => simp [MyNat.add, itadd]
  case succ => simp [MyNat.add, MyNat.add_succ, itadd, *]


/- @@@
## Trick 3: Generalizing the Induction Hypothesis

Often, the thing you want to prove is not "inductive" by itself. Meaning, that
you want to prove a goal `∀n. P(n)` but in fact you need to prove something stronger
like `∀n. P(n) /\ Q(n)` or even `∀n m, Q(n, m)` which then implies your goal.



### Example: Tail-Recursive `sum`

```
sum 3
=>
3 + sum 2
=>
3 + 2 + sum 1
=>
3 + 2 + 1 + sum 0
=>
3 + 2 + 1 + 0
```

@@@ -/

def sum (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | n' + 1 => n + sum n'

def loop (n res : Nat) : Nat :=
  match n with
  | 0      => res
  | n' + 1 => loop n' (res + n)

def sum_tr (n: Nat) := loop n 0

-- loop (n' + 1) 0 == sum (n' + 1)
-- loop a 0  == sum a
-- loop n res  == (sum n) + res

theorem loop_sum : ∀ n res, loop n res = (sum n) + res := by
  intros n res
  induction n generalizing res
  . case zero =>
    simp [loop, sum]
  . case succ n' ih =>
    simp_arith [loop, sum, ih]

theorem sum_eq_sum_tr : ∀ n, sum_tr n = sum n := by
  simp [sum_tr, loop_sum]




/-

fn sum(mut n: Nat) -> Nat {
  let mut res = 0
  while let S n' = n {
    res = res + n;
    n   = n';
  }
  res
}
-/








/- @@@

**Tail-Recursively Summing**

In an _iterative_ language you might write a **loop**
to sum the numbers `n + n-1 + ... + 0` e.g.

```rust
fn sum_tr(mut n: Nat) {
  let mut acc = 0;
  while let succ m = n {
    acc += n;
    n = m
  }
  return acc
}
```

We can write the above with **tail-recursion**

- The recursive call is the "last thing" the function does
- That is, the recursive result is returned without any further computation

**NOTE:** Go and look at `itadd`; is it tail recursive?

@@@-/

-- def sum_tr (n acc : Nat) : Nat :=
--   match n with
--   | 0 => acc
--   | n' + 1 => sum_tr n' (n + acc)

-- def sum' (n: Nat) := sum_tr n 0

/- @@@

Lets try to prove that `sum` and `sum'` always compute the *same result*.

@@@ -/



theorem sum_eq_sum' : ∀ n, sum n = sum' n := by
  intros n
  induction n
  sorry

/- @@@
Oops, we are stuck.

We need to know something about `sum_tr n' (n' + 1)` but what?

Can you think of a suitable helper lemma, which would let us directly
prove `sum_eq_sum'`?

```lean
theorem helper: ∀ n acc, sum_tr n acc = sum n + acc := by ...

theorem sum_eq_sum' : ∀ n, sum' n = sum n := by
  intros
  simp_arith [sum', helper]
```

@@@ -/



open List

/- @@@
### Example: Tail-Recursive `sum_list`
@@@ -/

/- @@@
**Summing a List***
@@@-/

def sum_list (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | x ::xs' => x + sum_list xs'

/- @@@
**Tail-Recursively Summing a List***

In an _iterative_ language you might write a **loop**
to sum the elements of a list, e.g.

```rust
fn sum_list(xs: List<Nat>) {
  let mut acc = 0;
  while let cons x ys = xs {
    acc += x;
    xs = ys
  }
  return acc
}
```

We can write the above with *tail-recursion* (where the recursive call is the "last thing")
that the function does. (Hint: Go and look at `itadd`; is it tail recursive?)

@@@-/

def sum_list_tr (xs : List Nat) (acc : Nat): Nat :=
  match xs with
  | [] => acc
  | x :: ys => sum_list_tr ys (acc + x)

def sum_list' (xs: List Nat) := sum_list_tr xs 0

/- @@@
Can you figure out a suitable helper lemma that would let us complete
the proof of `sum_list_eq_sum_list'` below?
@@@ -/

theorem sum_list'_eq : ∀ (xs acc), sum_list_tr xs acc = sum_list xs + acc := by
  sorry

theorem sum_list_eq_sum_list' : ∀ xs, sum_list' xs = sum_list xs := by
  intros xs
  simp_arith [sum_list', sum_list'_eq]


/- @@@
### Example: Tail-Recursive Reverse

```
rev_tr [0,1,2,3]
=>
loop [0,1,2,3] []
=>
loop [1,2,3] [0]
=>
loop [2,3] [1, 0]
=>
loop [3] [2, 1, 0]
=>
loop [] [3, 2, 1, 0]
=>
[3,2,1,0]
```

@@@ -/

def rev_tr {α : Type} (xs res: List α) : List α :=
  match xs with
  | [] => res
  | x ::xs' => rev_tr xs' (x :: res)

def rev' (xs: List α) := rev_tr xs []

example : rev' [0,1,2,3] = [3,2,1,0] := by rfl

/- @@@
Can you figure out a suitable helper lemma `rev_tr_app` that would let us complete
the proof of `rev_eq_rev'` below?

```
rev_tr xs [] == rev xs

rev_tr xs res
  == [xn, ...x3, x2,x1, 99]
  == rev xs ++ res
```

@@@ -/

theorem app_nil : ∀ {α : Type} (xs: List α), app xs [] = xs := by
  sorry

theorem rev_tr_helper_theorem : ∀ {α : Type} (xs res : List α),
  rev_tr xs res = app (rev xs) res := by sorry

theorem rev_eq_rev' : ∀ {α : Type} (xs: List α), rev' xs = rev xs := by
  intros α xs
  simp [rev', rev_tr_helper_theorem, app_nil]


/- @@@
### Example: Tail-Recursive Evaluator

**Arithmetic Expressions**
@@@ -/

inductive Aexp : Type where
  | const : Nat -> Aexp
  | plus  : Aexp -> Aexp -> Aexp
  deriving Repr

open Aexp

def two_plus_three := plus (const 2) (const 3)


/- @@@

```
     alice_plus
    /          \
   bob_const   bob_const
   |            |
   2            3
```

**Evaluating Expressions**
@@@-/

def eval (e: Aexp) : Nat :=
  match e with
  | const n => n
  | plus e1 e2 => eval e1 + eval e2

#eval eval two_plus_three

def eval_acc (e: Aexp) (res: Nat) : Nat :=
  match e with
  | const n => n + res
  | plus e1 e2 => eval_acc e2 (eval_acc e1 res)

def eval' (e: Aexp) := eval_acc e 0

example : eval' two_plus_three = eval two_plus_three := by rfl

/- @@@

```
eval' two_plus_three
=>
eval' (plus (const 2) (const 3))
=>
eval_acc (plus (const 2) (const 3)) 0
=>
eval_acc (const 3) (eval_acc (const 2) 0)
=>
eval_acc (const 3) ( 2 + 0)
=>
eval_acc (const 3) 2
=>
3 + 2
=>
5
```



### QUIZ: Is `eval_acc` tail recursive?

Lets try to prove that `eval'` and `eval` are "equivalent".

Can you figure out a suitable helper lemma that would let us complete
the proof of `eval_eq_eval'`?
@@@ -/

theorem magic_theorem : ∀ e res, eval_acc e res = eval e + res := by
  intros e res
  induction e generalizing res
  . case const n => rfl
  . case plus e1 e2 ih1 ih2 =>
    simp_arith [eval, eval_acc, ih1, ih2]

theorem eval_eq_eval' : ∀ e, eval e = eval' e := by
  intros e
  simp [eval', magic_theorem]




/- @@@
## Trick 4: Functional Induction

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
  | x::xs', y::ys' => x :: y :: alt xs' ys'

#eval alt [1,2,3,4] [10]

/- @@@
First, lets try a "brute force" proof.

```
exp ::= const c | var | plus exp exp | mult exp exp

(plus
  (mult
    (const 7)
    (mult (var (mult var var)))))
  (plus
    (mult (const 2) (mult var var))
    (const 10))
)

7x^3 + 2*x^2 + 10

5x^3 + 12*x^2

[7, 2, 0, 10]

[5, 12, 0, 0]

[12, 14, 0, 10]
```

@@@ -/

theorem alt_len_easy : ∀ {α : Type} (xs ys : List α),
  len (alt xs ys) = len xs + len ys := by
  intros α xs ys
  induction xs, ys using alt.induct
  . case case1 => simp [alt, len]
  . case case2 => simp [alt, len]
  . case case3 x xs' y ys' ih => simp_arith [alt, len, *]


theorem alt_len : ∀ {α : Type} (xs ys : List α),
  len (alt xs ys) = len xs + len ys := by
  intros α xs ys
  induction xs
  . case nil =>
    simp [alt, len]
  . case cons x xs' ih_xs =>
    induction ys
    . case nil =>
      simp [alt, len]
    . case cons y ys' ih_ys =>
      simp [alt, len, *]
      sorry





/- @@@
Instead, it can be easier to do the *same* induction as mirrors the recursion in `alt`
@@@ -/

theorem alt_len' : ∀ {α : Type} (xs ys : List α), len (alt xs ys) = len xs + len ys := by
  intros α xs ys
  induction xs, ys using alt.induct
  . case case1 => simp [alt, len]
  . case case2 => simp [alt, len]
  . case case3 => simp_arith [alt, len, *]
