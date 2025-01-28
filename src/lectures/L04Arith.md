```lean
set_option pp.fieldNotation false
```


# Expressions

This material is based on

- Chapter 3 of [Concrete Semantics](http://www.concrete-semantics.org/)


## Arithmetic Expressions

```lean
abbrev Val := Nat
abbrev Vname := String

inductive Aexp where
| num : Val -> Aexp
| var : Vname -> Aexp
| add : Aexp -> Aexp -> Aexp
deriving Repr

open Aexp

-- 5
def aexp_5 := num 5       -- 5

-- x
def aexp_x := var "x"     -- x

-- x + y
def aexp_x_plus_y := add (var "x") (var "y")    -- x + y

-- 2 + ( z + 3)
def aexp_2_plus_z_plus_3 := add (num 2) (add (var "z") (num 3))
```


## States

```lean
abbrev State := Vname -> Val

-- initial state
def st0 : State := fun _ => 0

-- state that maps "x" -> 10, "y" -> 20, _ -> 10000
def st_funny (v: Vname) : Val :=
  match v with
  | "x" => 10
  | "y" => 20
  | _   => 10000


-- update state
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y
```

## Evaluation

```lean
def aval (a: Aexp) (s: State) : Val :=
  match a with
  | num n => n
  | var x => s x
  | add a1 a2 => aval a1 s + aval a2 s

#eval aval aexp_x_plus_y st_funny





notation:10 st " [ " x " := " v " ] " => upd st x v

def st1 := st0 ["x" := 2] [ "y" := 10 ] [ "z" := 100 ]

example : aval aexp_5 st0 = 5 := rfl
example : aval aexp_x st0 = 0 := rfl

example : aval aexp_x_plus_y st1 = 12 := rfl
example : aval aexp_2_plus_z_plus_3 st1 = 105 := rfl
```

## Constant Folding

Compilers often want to "simplify" expressions by performing,
at compile time, various operations on constants.

For example, we may want to simplify an expression

```lean

x + (3 + 1)     ==> x + 4

add (var "x") (add (num 3) (num 1))
```

to just

```lean
add (var "x") (num 4)
```

We can implement this idea in a little recursive funciton `asimp_const`
that does this form of **constant folding** in a bottom-up manner



```lean
def asimp_const (a: Aexp) : Aexp :=
  match a with
  | num n => num n
  | var x => var x
  | add a1 a2 => match asimp_const a1, asimp_const a2 with
                 | num n1, num n2 => num (n1 + n2)
                 | a1', a2' => add a1' a2'

#eval asimp_const (add (var "x") (add (num 10) (num 20)))

#eval asimp_const (add (num 10) (add (var "x") (num 20)))
```


       add
      /   \
      x    add
          /    \
        10     20

       add
      /   \
     10    add
          /    \
         x     20



## Equivalence of Constant Folding

Lets prove that `asimp_const` does not **change the meaning** of the expression `a`.

```lean
theorem helper_asimp_const : forall a1 a2,
  aval (asimp_const (add a1 a2)) s = aval a1 s + aval a2 s := by
  intros a1 a2
  induction a1, a2 using asimp_const.induct
  . case case1 => sorry
  . case case2 => sorry
  . case case3 => sorry
  . case case4 => sorry

theorem aval_asimp_const : ∀ a s, aval a s = aval (asimp_const a) s  := by
  intros a s
  induction a using asimp_const.induct
  . case case1 =>
    rfl
  . case case2 =>
    rfl
  . case case3 a1 a2 n1 n2 ih2 ih1 ih2' ih1' =>
    simp [aval, asimp_const, *]
  . case case4 a1 a2 _ ih2 ih3 =>
    simp [aval, asimp_const, *]
```

## TACTIC: `simp_all` to simplify _hypotheses_

Lets flip the order of the equality.


```lean
-- REWRITING hypotheses: simp_all
theorem aval_asimp_const' : ∀ a s,
  aval (asimp_const a) s = aval a s := by
  intros a s
  induction a using asimp_const.induct
  . case case1 => rfl
  . case case2 => rfl
  . case case3 a1 a2 n1 n2 ih2 ih1 ih2' ih1' =>
    simp_all [aval, asimp_const]
  . case case4 a1 a2 _ ih2 ih3 =>
    simp_all [aval, asimp_const]
```

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

```lean
def smart_add (a1 a2: Aexp) : Aexp :=
  match a1, a2 with
  | num n1, num n2 => num (n1 + n2)
  | num n , a      => if n = 0 then a else add (num n) a
  | a, num n       => if n = 0 then a else add a (num n)
  | _, _           => add a1 a2
```

We can now write a general simplifier `asimp` that recursively
traverses the `Aexp` and invokes `plus` at each `add`

```lean
def asimp (a: Aexp) : Aexp :=
  match a with
  | num n => num n
  | var x => var x
  | add a1 a2 => smart_add (asimp a1) (asimp a2)
```


Lets try to prove that `asimp` does not change the meaning of an expression.





```lean
theorem asimp_helper : ∀ a1 a2 s,
  aval (smart_add a1 a2) s = aval a1 s + aval a2 s := by
  intros a1 a2 s
  cases a1 <;> cases a2 <;> simp [smart_add, aval] <;> split <;> simp [aval, *]

theorem aval_asimp_stuck : ∀ a s,
  aval a s = aval (asimp a) s := by
  intros a s
  induction a <;> simp [asimp, aval, asimp_helper, *]
```

Oof. The "direct" proof-by-induction is stuck. Can you think of a suitable "helper lemma"?

Yikes, we're stuck with a goal that looks like

```
⊢ aval (asimp a✝¹) s + aval (asimp a✝) s = aval (plus (asimp a✝¹) (asimp a✝)) s
```

We need a helper lemma that might tell us what `aval (plus a1 a2) s` _should_ evaluate to?

```lean
theorem aval_aplus : ∀ a1 a2 s,  aval (smart_add a1 a2) s = aval a1 s + aval a2 s := by
  intros a1 a2 s
  cases a1 <;> cases a2 <;> simp_arith [aval, smart_add] <;> split <;> simp_all!
```

We can use this helper to complete the proof

```lean
theorem aval_asimp : ∀ a s,
  aval a s = aval (asimp a) s := by
  intros a s
  induction a <;> simp [asimp, aval, aval_aplus, *]
```



## The **`split`** tactic

Hmm, now we're left with a goal that looks like

```
s : State
a✝¹ : Val
a✝ : Vname
⊢ aval (if a✝¹ = 0 then var a✝ else add (num a✝¹) (var a✝)) s = a✝¹ + s a✝
```

We need to "split-cases" on the `if a✝¹ = 0` branch ... convenient to do so with `split`
(and then keep `simp`-ing!)

```lean
theorem aval_aplus'' : ∀ a1 a2 s,  aval (smart_add a1 a2) s = aval a1 s + aval a2 s := by
  intros a1 a2 s
  cases a1 <;> cases a2 <;> simp_arith [aval, smart_add] <;> split <;> simp_all [aval]
```


## Boolean Expressions

Lets define a datatype for boolean expressions


```lean
inductive Bexp where
  | bbool : Bool -> Bexp
  | bnot  : Bexp  -> Bexp
  | band  : Bexp  -> Bexp -> Bexp
  | bless : Aexp  -> Aexp -> Bexp
  deriving Repr

open Bexp
```

## Boolean Evaluator

```lean
def bval (b: Bexp) (s: State) : Bool :=
  match b with
  | bbool v => v
  | bnot b' => !bval b' s
  | band b1 b2 => bval b1 s && bval b2 s
  | bless a1 a2 => aval a1 s < aval a2 s
```


## "Smart Constructors" for Boolean Constant Folding

```lean
def smart_and (b1 b2: Bexp) : Bexp :=
  match b1, b2 with
  | bbool true, _  => b2
  | bbool false, _ => bbool false
  | _, bbool true  => b1
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
```

## Smart Constructors are Equivalent

```lean
theorem smart_not_eq : ∀ b s, bval (smart_not b) s = bval (bnot b) s := by
  intros b s
  cases b
  . case bbool v => cases v <;> rfl
  . case bnot    => rfl
  . case band    => rfl
  . case bless   => rfl

theorem smart_and_eq : ∀ b1 b2 s,
  bval (smart_and b1 b2) s = bval (band b1 b2) s := by
  intros b1 b2 s
  cases b1 <;> cases b2 <;> simp [bval, smart_and] <;> split <;> simp_all [bval]

theorem smart_less_eq : ∀ a1 a2 s, bval (smart_less a1 a2) s = bval (bless a1 a2) s := by
  intros a1 a2 s
  cases a1 <;> cases a2 <;> simp [bval, smart_less, aval]
```

## Correctness of Boolean Simplification

Lets prove that `bval_bsimp b` does not
*change the meaning* of an expression `b`.


```lean
theorem bval_bsimp_stuck : ∀ b s,
  bval b s = bval (bsimp b) s := by
  intros b s
  induction b
  . case bbool => simp [bsimp]
  . case bnot  => simp [bval, bsimp, smart_not_eq, *]
  . case band  => simp [bval, bsimp, smart_and_eq, *]
  . case bless => simp [bval, bsimp, smart_less_eq, <-aval_asimp]
```


## Backwards Rewriting / Simplification

Boo! We cannot use `aval_asimp` directly.

The `simp` uses a theorem of the form `lhs = rhs`
to rewrite occurrences of `lhs` with `rhs`.
In this case, however,

- the theorem `aval_asimp` says `aval a s = aval (asimp a) s`

- but the goal contains a term `aval (asimp a') s`

- where we want to rewrite the RHS of the theorem with the LHS!

You can do this either by

1. making a _new_ theorem where the LHS and RHS are flipped (which is a bit silly...)

2. or instead by specifying `<-` in the `simp` tactic.

```lean
theorem bval_bsimp : ∀ b s, bval b s = bval (bsimp b) s := by
  intros b s
  induction b
  . case bbool => simp [bsimp]
  . case bnot  => simp [bval, bsimp, smart_not_eq, *]
  . case band  => simp [bval, bsimp, smart_and_eq, *]
  . case bless => simp [bval, bsimp, smart_less_eq, <-aval_asimp]
```

## Case Study: Compiling to a Stack Machine

In this case study, we will define a "stack machine" that operates on a stack of values.

**Intuition**

Given an `a : Aexp` , say

```
Aexp=65, Instrs = [PUSH 65]
Aexp=10, Instrs = [PUSH 10]

Aexp=65 + 10, Instrs = [PUSH 10, PUSH 65, ADD]
Aexp=e1 + e2, Instrs = [PUSH 10, PUSH 65, ADD]
                       comp e2 ++ comp e1 ++ ADD


PUSH 10, PUSH 65, ADD

  []
PUSH 10
  [10]
PUSH 65
  [65, 10]
ADD
  [65 + 10]




((65 + 10) + (5 + 92))



            []
PUSH 10
            [10]
PUSH 65
            [65, 10]
ADD
            [75]
PUSH 92
            [92, 75]
PUSH 5
            [5, 92, 75]
ADD
            [97, 75]
ADD
            [172]


[x |--> 5555, y |--> 6666]

((x + 10) + (y + 92))

                []
PUSH 10
                [10]
PUSHVAR x
                [5555, 10]
ADD
                [5565]
PUSH 92
                [92, 5565]
PUSHVAR y
                [6666, 92, 5565]
ADD
                [6758, 5565]
ADD
                [12323]


PUSH n
ADD

            [ ]
PUSH 10
            [10]
PUSH 20
            [20,10]
ADD
            [30]



((x + 10) + (5 + y))
```

We will compile it into a sequence of "instructions" that operate on a stack.

```
LOAD x
LOADI 10
ADD
LOADI 5
LOAD y
ADD
ADD
```

Lets *execute* this sequence of instructions on a state `s` defined as `[x |-> 100, y |-> 200]` as

```
[]
--> LOAD x
[100]
--> LOADI 10
[10, 100]
--> ADD
[110]
--> LOADI 5
[5, 110]
--> LOAD y
[200, 5, 110]
--> ADD
[205, 110]
--> ADD
[315]
```

Note that the final result left on the stack is `315` which is exactly what `aval a s` would return.

Let's define a "compiler" and "exec" function and prove that the compiler is correct!

### Stack Machine: Instructions

```lean
inductive Instr where
  | PUSH    : Val -> Instr
  | PUSHVAR : Vname -> Instr
  | ADD     : Instr
  deriving Repr

open Instr
```




### Stack Machine: Interpreter

A `Stack` is just a list of values

```lean
abbrev Stack := List Val

def exec1' (instr: Instr) (s: State) (stk: Stack) : Stack :=
  match instr with
  | PUSH n    => n :: stk
  | PUSHVAR x => (s x) :: stk
  | ADD       => match stk with
                 | (n1 :: n2 :: rest) => (n1 + n2) :: rest
                 | _ => []

def exec' (is: List Instr) (s: State) (stk : Stack) : Stack :=
  match is with
  | []     => stk
  | i::is' => exec' is' s (exec1' i s stk)

def comp' (a: Aexp) : List Instr :=
  match a with
  | num n => [PUSH n]
  | var x => [PUSHVAR x]
  | add a1 a2 => comp' a2 ++ comp' a1 ++ [ADD]

def a0 : Aexp := add
                     (add (var "x") (num 10))
                     (add (num 5) (var "y"))

def st0' (v: Vname) : Val := if v = "x" then 100 else if v = "y" then 1000 else 0

theorem compiler_test : [aval a0 st0'] = exec' (comp' a0) st0' [] := by rfl

/-

exec' ([i1, i2, i3] ++ rest) s stk
=>
exec' [i2,i3,...] s (exec1' i1 s stk)
=>
exec' rest s (exec1' i3 s (exec1' i2 s (exec1' i1 s stk)))
             (exec' is1 s stk)

-/

theorem exec_append' : ∀ is1 is2 s stk,
  exec' (is1 ++ is2) s stk = exec' is2 s (exec' is1 s stk) := by
  intros is1 is2 s stk
  induction is1 generalizing stk
  . case nil =>
    rfl
  . case cons i is ih =>
    simp [exec', *]


theorem compiler_correct : ∀ a s stk,
  exec' (comp' a) s stk = (aval a s :: stk) := by
  intros a s
  induction a generalizing s
  . case num =>
    simp [comp', exec', exec1', aval]
  . case var =>
    simp [comp', exec', exec1', aval]
  . case add a1 a2 ih1 ih2 =>
     simp [comp', exec', exec1', aval, exec_append', *]
```


Aexp -> List Instr

Here's a function `exec1` that executes a *single* instruction


```lean
def exec1 (s:State) (i:Instr) (stk:Stack) : Stack :=
  match i, stk with
  | PUSH n, _         => (n :: stk)
  | PUSHVAR  x, _         => (s x :: stk)
  | ADD    , n::m::stk => (m + n) :: stk
  | ADD    , _         => []
```

Here's a function `exec` that executes a *sequence* of instructions by invoking `exec1` on each instruction.

```lean
def exec (s:State) (is: List Instr) (stk:Stack) : Stack :=
  match is with
  | []     => stk
  | i::is' => exec s is' (exec1 s i stk)
```


### Stack Machine: Compiler

Here's a function that "compiles" an `Aexp` into a `List Instr`


```lean
def comp (a: Aexp) : List Instr :=
  match a with
  | num n => [PUSH n]
  | var x => [PUSHVAR  x]
  | add a1 a2 => comp a1 ++ comp a2 ++ [ADD]
```

### Proving Compiler Correctness

```lean
theorem comp_exec_stuck : ∀ {s : State} {a : Aexp} { stk : Stack },
  exec s (comp a) stk = aval a s :: stk := by
  intro s a stk
  induction a generalizing s stk
  case num n => rfl
  case var x => rfl
  case add a1 a2 ih1 ih2 => simp_all [comp, aval, exec, exec1]; sorry
```

Oh no! We're stuck, what helper lemma do we need?

```lean
theorem comp_exec : ∀ {s : State} {a : Aexp} { stk : Stack },
  exec s (comp a) stk = aval a s :: stk := by
  intro s a stk
  induction a generalizing s stk
  case num n => rfl
  case var x => rfl
  case add a1 a2 ih1 ih2 => simp_all [comp, aval, exec, exec1]; sorry
```

