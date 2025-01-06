/- @@@

# Expressions, Types and Functions

This material is based on sections 1-3 of [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/getting-to-know.html)

## Expressions

In lean, programs are built from *expressions* which (if well-typed) have a *value*.

| **Expression**  |  **Value** |
|:----------------|:-----------|
| `1 + 2`         | `3`        |
| `3 * 4`         | `12`       |
| `1 + 2 * 3 + 4` | `11`       |

Lean expressions are *mathematical* expressions as in Haskell, Ocaml, etc.
* variables get a "bound" to a _single_ value (no "re-assignment"),
* expressions always evaluate to the _same_ value ("no side effects")
* if two expressions have the same value, then replacing one with
the other will not cause the program to compute a different result.

To evaluate an expression, write `#eval` before it in your editor,
and see the result by hovering over `#eval`.

@@@ -/

#eval 1 + 2

#eval 3 * 4

#eval 1 + 2 * 3 + 4


/- @@@

## Types

*Every lean expression has a type*.

The *type* tells lean -- *without* evaluating the expression -- what
kind of value it will produce.

Why do Programming Languages need types???





Lean has a _very_ sophisticated type system that we will learn more about soon...

To see the type of an expression, write `#check` before it in your editor,


### Primitive: `Nat`

Lean has a "primitive" type `Nat` for natural numbers (0, 1, 2, ...) that we saw
in the expressions above.

@@@ -/

#check 1      -- Nat (natural number i.e. 0, 1, 2,...)

#check 1 + 2  -- Nat




/- @@@

**QUIZ** What is the value of the following expression?

@@@ -/

#eval 5 - 10



/- @@@

## Type Annotations

Sometimes lean can *infer* the type automatically.

But sometimes we have to (or want to) give it an *annotation*.


### Primitive: `Int`

@@@ -/

#check (1 : Int)      -- Int (..., -2, -1, 0, 1, 2,...)

#check (1 + 2 : Int)  -- Int

/- @@@
**QUIZ** What is the value of the following expression?
@@@ -/

#eval (5 - 10 : Int)


/- @@@
### Primitive: `Float`
   @@@ -/

#check 1.1      -- Float

#eval 1.1 + 2.2

/- @@@
### Primitive: `Bool`
   @@@ -/


#eval true
#check true   -- Bool

#eval false
#check false  -- Bool

#eval true  && true
#eval true  && false
#eval false && true
#eval false && false

#eval true  || true
#eval true  || false
#eval false || true
#eval false || false

-- #eval false + 10    -- type error!

/- @@@
### Primitive: `String`
   @@@ -/

#eval "Hello, " ++ "world!"
#check "Hello, " ++ "world!"  -- String

-- #eval "Hello, " ++ 10   -- type error!

-- #eval "Hello, " ++ world   -- unknown identifier!


/- @@@
## Definitions

We can *name* expressions using the `def` keyword.
@@@ -/

def hello := "hello"
def world := "world"
def one := 1
def two := 2
def five_plus_ten   := 5 + 10
def five_minus_ten  := 5 - 10
def five_minus_ten' : Int := 5 - 10

/- @@@
You can now `#check` or `#eval` these definitions.
@@@ -/

#check hello
#eval hello
#eval hello ++ world
#eval five_minus_ten
#eval five_minus_ten'

/- @@@
## Functions

In lean, functions are also expressions, as in the λ-calculus.
@@@ -/

#check (fun (n : Nat) => n + 1)         -- Nat -> Nat
#check (λ (n : Nat) => n + 1)           -- Nat -> Nat

#check (fun (x y : Nat) => x + y)       -- Nat -> Nat -> Nat -> Nat
#check (λ (x y : Nat) => x + y)         -- Nat -> Nat -> Nat -> Nat


/- @@@
**QUIZ** What is the *type* of the following expression?
@@@ -/

#check (fun (x y : Nat) => x > y)

/- @@@
## Function Calls

You can *call* a function by putting the arguments in front
@@@ -/

#eval (fun x => x + 1) 10

#eval (fun x y => x + y) 10 20


/- @@@
**QUIZ** What is the *value* of the following expression?
@@@ -/

#eval (fun x y => x > y) 10 20


/-@@@
## Function Definitions

Of course, it is more convenient to *name* functions as well, using `def`
since naming allows us to *reuse* the function in many places.
@@@-/

def inc := fun (x : Int)  => x + 1

#eval inc 10
#eval inc 20
-- #eval inc true  -- type error!

def add := fun (x y : Nat) => x + y

#eval add 10 20

/- @@@

It is often convenient to write the parameters of the function *to the left*

The below definitions of `inc'` and `add'` are equivalent to the above definitions of `inc` and `add`.

@@@ -/

def inc' (x : Int) : Int := x + 1

#eval inc' 10     -- 11


def add' (x y : Nat) : Nat := x + y

#eval add' 10 20  -- 30

/- @@@
**EXERCISE** Write a function `max` that takes two `Nat`s and returns the maximum of the two.

**EXERCISE** Write a function `max3` that takes three `Nat`s and uses `max` to compute the maximum of all three

**EXERCISE**
    Write a function `joinStringsWith` of type `String -> String -> String -> String`
    that creates a new string by placing its first argument between its second and third arguments.
@@@ -/

-- #eval joinStringsWith ", " "this" "that"  -- "this, that"
-- #check joinStringsWith ", " -- **QUIZ** What is the type of the expression on the left?

/- @@@
**EXERCISE**
Write a function `volume` of type `Nat -> Nat -> Nat -> Nat` which computes
the volume of a brick given `height`, `width`, and `depth`.
@@@ -/
