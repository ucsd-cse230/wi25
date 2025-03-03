
import Cse230wi25.L05Evidence

set_option pp.fieldNotation false
set_option pp.proofs true

/- @@@

# Type Soundness via Small-Step Semantics

Next, lets look at a concrete application of *small-step* semantics: to prove the correctness of a type checker.

## Floating IMP

Our old `IMP` language has no type-safety issues because, well, every variable is simply a `Nat`.

Let us extend the set of possible `Val` to include *floating* point values as well.

@@@ -/


inductive Val where
  | Iv : Int -> Val
  | Fv : Float -> Val
  deriving Repr

open Val

/- @@@
We can have *integer* values like
@@@ -/

#eval (Iv 12)

/- @@@
Or *floating point* values like
@@@ -/

#eval (Fv 3.14)


/- @@@

As before,

- an *identifier* or *variable* `Vname` is just a `String` and
- a `State` maps `Vname` to `Val` (which is either an `Int` or a `Float`).

@@@ -/

abbrev Vname := String

abbrev State := Vname -> Val

@[simp] def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v

/- @@@

### Arithmetic and Boolean Expressions

Finally, we can extend `Aexp` to include `Int` and `Float` constants, together with
the usual binary operations as:

@@@ -/



inductive Aexp where
  | Ic  : Int -> Aexp            -- integer constant
  | Fc  : Float -> Aexp          -- floating point constant
  | V   : Vname -> Aexp          -- variable
  | Add : Aexp -> Aexp -> Aexp   -- addition
  deriving Repr

open Aexp

inductive Bexp where
  | Bc   : Bool -> Bexp
  | Not  : Bexp -> Bexp
  | And  : Bexp -> Bexp -> Bexp
  | Less : Aexp -> Aexp -> Bexp
  deriving Repr

open Bexp



class ToAexp (a : Type) where
  toAexp : a -> Aexp


instance : OfNat Aexp (n: Nat) where
  ofNat := Ic n

instance : ToAexp Int where
  toAexp := Ic

instance : ToAexp String where
  toAexp := V

instance : Add Aexp where
  add := fun a1 a2 => Add a1 a2

instance : HAdd String Aexp Aexp where
  hAdd := fun s a => Add (V s) a

instance : HAdd String Int Aexp where
  hAdd := fun s a => Add (V s) (Ic a)

def mkVar (s: String) (i : Nat) : Aexp := V (s!"{s}_{i}")

notation:80 lhs:91 "#" rhs:90 => mkVar lhs rhs

def x := "x"
def y := "y"
def z := "z"

def aexp0 : Aexp := x#1 + y#1 + z#1 + 5

#eval aexp0

/- @@@

### Evaluating Expressions

Can you think about why it is a bit tedious (but not impossible!)
to define `aval` for this new `Aexp`?

So, instead lets define the evaluation of `Aexp` using
an `inductive` predicate, where we need only define the
cases where a value is produced and we can *omit* the
cases where an `Int` is added to / compared against a `Float`.

@@@ -/


inductive Taval : Aexp -> State -> Val -> Prop where

  | T_Ic  : ∀ {i s},
            Taval (Ic i) s (Iv i)

  | T_Rc  : ∀ {f s},
            Taval (Fc f) s (Fv f)

  | T_V   : ∀ {x s},
            Taval (V x) s (s x)

  | T_AddI : ∀ {a1 a2 s i1 i2},
             Taval a1 s (Iv i1) -> Taval a2 s (Iv i2) ->
             Taval (Add a1 a2) s (Iv (i1 + i2))

  | T_AddF : ∀ {a1 a2 s r1 r2},
             Taval a1 s (Fv r1) -> Taval a2 s (Fv r2) ->
             Taval (Add a1 a2) s (Fv (r1 + r2))

open Taval

inductive Tbval : Bexp -> State -> Bool -> Prop where

  | T_Bc  : ∀ {v s},
            Tbval (Bc v) s v

  | T_Not : ∀ {b v s},
            Tbval b s v ->
            Tbval (Not b) s (!v)

  | T_And : ∀ {b1 b2 v1 v2 s},
            Tbval b1 s v1 -> Tbval b2 s v2 ->
            Tbval (And b1 b2) s (v1 && v2)

  | T_LessI : ∀ {a1 a2 i1 i2 s},
              Taval a1 s (Iv i1) -> Taval a2 s (Iv i2) ->
              Tbval (Less a1 a2) s (i1 < i2)

  | T_LessF : ∀ {a1 a2 r1 r2 s},
              Taval a1 s (Fv r1) -> Taval a2 s (Fv r2) ->
              Tbval (Less a1 a2) s (r1 < r2)

open Tbval


def st0 : State := fun x => match x with
  | "x" => Iv 3
  | "y" => Iv 4
  | _   => Iv 0

/- @@@

### Floating Commands

Next, as with plain IMP, we define the type `Com`
of commands, now using the new `Aexp` and `Bexp`.

@@@ -/

inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  deriving Repr

open Com

infix:10 "<<"  => fun x y => Less x y
infix:10 "<~"  => Com.Assign
infixr:8 ";;" => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

/- @@@

And we can define a `SmallStep` operational semantics
for `Com` similar to that from the previous lecture.

**NOTE** Instead of using the *functions* `aval` and `bval`
we simply use the *relations* `Taval` and `Tbval`.

@@@ -/

abbrev Configuration := (Com × State)


inductive Step : Configuration -> Configuration -> Prop where

   | Assign : ∀ {x a s v},
                Taval a s v ->
                Step (x <~ a, s) (Skip, s [x := v])

   | Seq1   : ∀ {c s},
                Step ((Skip ;; c), s) (c, s)

   | Seq2   : ∀ {c1 c1' c2 s s'},
                Step (c1, s) (c1', s') ->
                Step ((c1 ;; c2) , s) ((c1' ;; c2), s')

   | IfTrue : ∀ {b c1 c2 s},
                Tbval b s true ->
                Step (IF b THEN c1 ELSE c2, s) (c1, s)

   | IfFalse : ∀ {b c1 c2 s},
                Tbval b s false ->
                Step (IF b THEN c1 ELSE c2, s) (c2, s)

   | While   : ∀ { b c s },
                Step (Com.While b c, s) (Com.If b (c ;; (Com.While b c)) Skip, s)

notation:12 cs "~~>" cs' => Step cs cs'

/- @@@

### Getting Stuck / Going Wrong

Now that we have `Int` and `Float` values, we have introduced the possibility
of programs **going wrong**. For example, we have not defined the meaning of
`Add (Ic 2) (Fc 3.1)` because doing so would require adding an `Int` and a
`Float` which (suppose we don't have any "casting") is meaningless.

In that case, a program like

```
x <~ Ic 2 ;;
y <~ Fc 3.1 ;;
z <~ x + y ;;
...
```

is *also* meaningless because the addition would **get stuck**.

How can we make sure that programs are "ok", that is, they **do not get stuck**?

## Type Checking

Well, this is precisely what **type checking** was invented to solve: to **predict** --
right when you *write* your code, that under no circumstances would execution get stuck
or go wrong because you mixed up the wrong values for some operation.

### Types

For our simple `FIMP` we require just two types "int" and "float" and so we can model
these as a new (lean) type `Ty` with the constructors (values) `TInt` and `TFloat`

@@@ -/

inductive Ty where
  | TInt : Ty
  | TFloat : Ty
  deriving Repr

/- @@@

### Environments

Next, we need a *table* or a *map* that records the `Ty` for each program variable.
Often this structure is called a **Type `Environment`** and in PL papers, written
using the letter `Γ`

@@@ -/


open Ty

abbrev Env := Vname -> Ty

/- @@@
For example, here is an `Env`ironment where *every* variable is presumed to be an integer.
@@@ -/

@[simp] def Γᵢ : Env := fun _ => TInt


/- @@@

### Typing Judgments

In Floyd-Hoare logic we proved propositions of the form `{p} c {q}`
that said, roughly, that

**IF**

- we start execution in a *pre-state* where `p` was true and
- execution of `c` terminates in some *post-state*

**THEN**

- the *post-state* will satisfy the assertion `q`


Similarly, with type systems we will prove propositions
of the form `Γ ⊢ e : τ` which say that

**IF**

- the variables in `e` are assumed to have the types given in `Γ`

**THEN**

- the expression `e` can be determined to have the type `τ`

We say that `e` **has-type** `τ` in environment `Γ`.

### Typing Rules for Arithmetic Expressions

Next, lets write down some **rules** that establish this `HasType` relation,
for each of the different kinds of `Aexp` and `Bexp`. The rules should let
us establish the proposition that `Γᵢ ⊢ x + (10 + y) : int` i.e. `x + (10 + y)` has
the type `int` in an environment where all the variables are of type `int`.

We want the rules to be **syntax-directed** meaning a **single rule** should
apply for each kind of expression. (Why?)


```

----------------[int]
Γ ⊢ 3 : ???


----------------[float]
Γ ⊢ 3.14 : ???


----------------[var]
Γ ⊢ x : ???


--------------------[add]
Γ ⊢ a1 + a2 : ???
```

@@@ -/


inductive HasTyA : Env -> Aexp -> Ty -> Prop where

  | Ty_Ic : ∀ {Γ i},
            HasTyA Γ (Ic i) TInt

  | Ty_Fc : ∀ {Γ r},
            HasTyA Γ (Fc r) TFloat

  | Ty_V  : ∀ {Γ x},
            HasTyA Γ (V x) (Γ x)

  | Ty_AddI : ∀ {Γ a1 a2},
              HasTyA Γ a1 TInt -> HasTyA Γ a2 TInt ->
              HasTyA Γ (Add a1 a2) TInt

  | Ty_AddF : ∀ {Γ a1 a2},
              HasTyA Γ a1 TFloat -> HasTyA Γ a2 TFloat ->
              HasTyA Γ (Add a1 a2) TFloat


notation:10 Γ " ⊢ " a " : " τ => HasTyA Γ a τ

/- @@@

Let us check our example

                      -------------[int]    -------------[var]
                      Γᵢ ⊢ 10 : int         Γᵢ ⊢ y : int
------------[var]     -----------------------------------[addI]
Γᵢ ⊢ x : int          Γᵢ ⊢ (10 + y) : int
-----------------------------------------[addI]
Γᵢ ⊢ x + (10 + y) : int

Lets see why having **syntax directed** rules is useful!

@@@ -/

example : Γᵢ ⊢ (V x + (Ic 10 + V y)) : TInt := by
  sorry



/- @@@
### Typing Rules for Boolean Expressions

Next, lets work out the rules for `Bexp` -- here we can just write
`Γ ⊢ b` (and leave out `: bool` because?)


```
???
---------------
Γ ⊢ true : ???


???
---------------[not]
Γ ⊢ ¬ b : ???


???
-------------------[and]
Γ ⊢ b1 /\ b2 : ???

???
--------------------[less]
Γ ⊢ a1 < a2 : ???
```
@@@ -/


inductive HasTyB : Env -> Bexp -> Prop where
  | Ty_Bc   : ∀ {Γ v},
              HasTyB Γ (Bc v)

  | Ty_Not  : ∀ {Γ b},
              HasTyB Γ b ->
              HasTyB Γ (Not b)

  | Ty_And  : ∀ {Γ b1 b2},
              HasTyB Γ b1 -> HasTyB Γ b2 ->
              HasTyB Γ (And b1 b2)

  | Ty_Less : ∀ {Γ a1 a2 t} ,
              HasTyA  Γ a1 t -> HasTyA Γ a2 t ->
              HasTyB Γ (Less a1 a2)

notation:10 Γ " ⊢ " a  => HasTyB Γ a

/- @@@

Again, the **syntax-directed** nature of the rules
makes establishing the "has-type" facts super easy!

@@@ -/

example : Γᵢ ⊢ (V x + (Ic 10 + V y)) << Ic 29 := by
  sorry

/- @@@

### Typing Rules for Commands

Finally, lets work out the rules for typing commands.

What does the **typing judgment** for a command look like?

#### QUIZ

Should the following hold?

```
Γᵢ ⊢ x <~ 10 ;; Skip ;; y <~ 10 ;; z <~ x + y
```


```
Γᵢ ⊢ x <~ 10 ;; Skip ;; y <~ 1.0 ;; z <~ x + y
```

What should the rules look like so that we can establish / reject appropriately?


@@@ -/

inductive HasTyC : Env -> Com -> Prop where
  | Ty_Skip   : ∀ {Γ},
                HasTyC Γ Skip

  | Ty_Assign : ∀ {Γ x a},
                HasTyA Γ a (Γ x) ->
                HasTyC Γ (x <~ a)

  | Ty_Seq    : ∀ {Γ c1 c2},
                HasTyC  Γ c1 -> HasTyC Γ c2 ->
                HasTyC Γ (c1 ;; c2)

  | Ty_If     : ∀ {Γ b c1 c2},
                HasTyB Γ b -> HasTyC Γ c1 -> HasTyC Γ c2 ->
                HasTyC Γ (IF b THEN c1 ELSE c2)

  | Ty_While  : ∀ {Γ b c},
                HasTyB Γ b -> HasTyC Γ c  ->
                HasTyC Γ (WHILE b DO c END)

notation:10 Γ " ⊢ " c  => HasTyC Γ c

-- Yay for syntax directed!
example : Γᵢ ⊢ "x" <~ Ic 3 ;; "y" <~ (V "x") + (Ic 4) := by
  repeat constructor

/- @@@

## Type Soundness

Ok great, so we made up a system of "type checking" rules.

But how do we know the rules are *sensible* or *meaningful* ?

How do we know the rules actually tell us something about the programs *execution*?

That is, right now we have defined *two* semantics for FIMP:

- **Dynamic Semantics** i.e. how the programs **run** via the `SmallStep` operational semantics; and

- **Static Semantics** i.e. how the programs **type-check** via the `HasTy` rules.

How can we *relate* or *connect* these two descriptions of program behavior?

Ultimately, we want to **prove** that

- *If* the program was _well-typed_ (statically)
- *Then* the program will not _go bad_ (dynamically).

But how can we state this property precisely as a theorem?



**Preservation** If the program does something THEN that thing is *expected* or *predicted*

**Progress** The program *does* something.





Let's try to formalize this in Lean, for *arith* expressions, *bool* expressions and then *commands*.

@@@ -/

/- @@@
### Types and their Values

First, let us write down the relationship between each **value** and its corresponding **type**.

@@@ -/

@[simp] def type(v: Val) : Ty := match v with
  | Iv _ => TInt
  | Fv _ => TFloat

/- @@@

A `State` `s` is **well-formed** with respect to a type environment `Γ` if every variable's value in `s`
is that specified in `Γ`
@@@ -/

@[simp] def Wf (Γ: Env) (s: State) : Prop :=
  ∀ x, Γ x = type (s x)

notation:10 Γ " ⊧ " s  => Wf Γ s


/- @@@
### Arithmetic

Lets start with *specifying* the *preservation* and *progress* properties for `Aexp`

**Preservation**

If the program does something THEN that thing is *expected* or *predicted*

If the `AExp`  does `__________________________` THEN `____________________________`


```
∀ { a } ,

  __________________________________________ ->

  __________________________________________
```


**Progress** The program *does* something.

```
∀ { a } ,

  __________________________________________ ->

  __________________________________________
```

@@@ -/

/- @@@

### Preservation

Now, lets try to prove it!

@@@ -/

theorem arith_preservation : ∀ { Γ a τ s v },
  (Γ ⊧ s) -> (Γ ⊢ a : τ) -> Taval a s v -> type v = τ
  := by
  intros Γ a τ s v G_s G_a_t a_s_v
  induction G_a_t generalizing v
  . case Ty_Ic i => cases a_s_v; simp_all
  . case Ty_Fc f => cases a_s_v; simp_all
  . case Ty_V x  => cases a_s_v; simp_all
  . case Ty_AddI a1 a2 _ _ ih1 _ =>
    cases a_s_v
    . simp_all
    . rename_i _ _ av1 _; apply (ih1 av1)
  . case Ty_AddF a1 a2 _ _ ih1 _ =>
    cases a_s_v
    . rename_i _ _ av1 _; apply (ih1 av1)
    . simp_all

/- @@@
### Progress

Now, lets try to prove it!
@@@ -/

theorem arith_progress': ∀ { Γ a τ s },
  (Γ ⊧ s) -> (Γ ⊢ a : τ) ->  ∃ v, Taval a s v  := by
  intros Γ a τ s G_s G_a_t
  induction G_a_t
  . case Ty_Ic i => repeat constructor
  . case Ty_Fc f => repeat constructor
  . case Ty_V x  => repeat constructor
  . case Ty_AddI => sorry
  . case Ty_AddF => sorry

/- @@@
The (slightly) tricky bit is to prove the progress for `a1 + a2` expressions.
Lets try to figure out what a helper lemma would look like!
@@@ -/

@[simp] def ty_val (t:Ty) (v:Val) : Prop :=
  match t with
  | TInt => ∃ n, v = Iv n
  | TFloat => ∃ n, v = Fv n

theorem arith_preservation_val : ∀ { Γ s a τ v },
  (Γ ⊧ s) -> (Γ ⊢ a : τ) -> Taval a s v -> ty_val τ v
  := by
  intros Γ s a τ v _ _ _
  have hv : type v = τ := by apply arith_preservation; repeat assumption
  cases v <;> simp_all [<-hv]

theorem add_progress: ∀ {Γ a1 a2 τ s},
  (Γ ⊧ s) -> (Γ ⊢ a1 : τ) -> (Γ ⊢ a2 : τ) ->
  (∃ v1, Taval a1 s v1) -> (∃ v2, Taval a2 s v2) ->
  ∃ v, Taval (a1 + a2) s v
  := by
  intros Γ a1 a2 τ s gs gt1 gt2 av1 av2
  cases av1; cases av2; rename_i v1 _ v2 _
  have h1' : ty_val τ v1 := by
    apply arith_preservation_val
    assumption; apply gt1; assumption
  have h2' : ty_val τ v2 := by
    apply arith_preservation_val
    assumption; apply gt2; assumption
  cases τ
  . case TInt   => cases h1'; cases h2'; simp_all; constructor; apply T_AddI; repeat assumption
  . case TFloat => cases h1'; cases h2'; simp_all; constructor; apply T_AddF; repeat assumption

/- @@@
Now we can use `add_progress` to complete the proof of `arith_progress`.
@@@ -/

theorem arith_progress: ∀ { Γ a τ s },
  (Γ ⊧ s) -> (Γ ⊢ a : τ) ->  ∃ v, Taval a s v  := by
  intros Γ a τ s G_s G_a_t
  induction G_a_t
  . case Ty_Ic i => repeat constructor
  . case Ty_Fc f => repeat constructor
  . case Ty_V x  => repeat constructor
  . case Ty_AddI => apply add_progress; repeat assumption
  . case Ty_AddF => apply add_progress; repeat assumption




/- @@@
### Boolean Expressions

These more or less follow the same structure as the
arithmetic expressions, except that instead `a1 < a2`
requires a bit of elbow grease, similar to `add_progress`.

**QUESTION** Why don't we need a `bool_preservation` theorem???
@@@ -/

theorem less_progress : ∀ {Γ a1 a2 s v1 v2 τ},
  (Γ ⊧ s) -> (Γ ⊢ a1 : τ) -> (Γ ⊢ a2 : τ) ->
  (Taval a1 s v1) -> (Taval a2 s v2) ->
  ∃ v, Tbval (a1 << a2) s v
  := by
  intros Γ a1 a2 s v1 v2 τ gs gt1 gt2 av1 av2
  have h1' : ty_val τ v1 := by
    apply arith_preservation_val
    assumption; apply gt1; assumption
  have h2' : ty_val τ v2 := by
    apply arith_preservation_val
    assumption; apply gt2; assumption
  cases τ
  . case TInt   => cases h1'; cases h2'; simp_all; constructor; apply T_LessI; repeat assumption
  . case TFloat => cases h1'; cases h2'; simp_all; constructor; apply T_LessF; repeat assumption

theorem bool_progress: ∀ { Γ s } { b : Bexp },
  (Γ ⊧ s) -> (Γ ⊢ b) -> ∃ v, (Tbval b s v)
  := by
  intros Γ s b Gs Gb
  induction Gb
  . case Ty_Bc v =>
    repeat constructor
  . case Ty_Not b' gb' ih =>
    cases ih
    repeat constructor
    assumption
  . case Ty_And b1 b2 Gb1 Gb2 ih1 ih2 =>
    cases ih1; cases ih2
    repeat constructor
    repeat assumption
  . case Ty_Less a1 a2 τ Ga1 Ga2 =>
    have h1 : ∃ v1, Taval a1 s v1 := by apply arith_progress; repeat assumption
    have h2 : ∃ v2, Taval a2 s v2 := by apply arith_progress; repeat assumption
    cases h1; cases h2; apply less_progress; repeat assumption

-------------------

/- @@@
### Commands

What should "preservation" and "progress" theorems look like for `Com` ?

**Preservation**

If the program does something THEN that thing is *expected* or *predicted*

If the `Com`  does `__________________________` THEN `____________________________`


```
∀ { c } ,

  __________________________________________ ->

  __________________________________________
```


**Progress** The program *does* something.

```
∀ { c } ,

  __________________________________________ ->

  __________________________________________
```

@@@ -/

/- @@@

#### Commands: Preservation

Let us split the preservation into two *separate* theorems the `Com` and `State` parts of the `Configuration`.
Preservation follows directly by manipulating the typing rules.

@@@ -/

theorem preservation1_com : ∀ { Γ } { c c' : Com } { s s' : State },
  (Γ ⊧ s) -> (Γ ⊢ c) -> ((c, s) ~~> (c', s')) -> (Γ ⊢ c')
  := by
  intros Γ c c' s s' wf_s ty_c step
  induction ty_c generalizing c' s s' <;> cases step <;> repeat trivial
  . case Ty_Assign.Assign => constructor
  . case Ty_Seq.Seq2      => rename_i ih _ _ _; constructor; apply ih; repeat trivial
  . case Ty_While         => repeat (constructor <;> repeat trivial)

theorem update_ty : ∀ { Γ s x v },  (Γ ⊧ s) -> (type v = Γ x) -> (Γ ⊧ s [x := v]) := by
  intros Γ s x v v_ty_x wf_s y
  by_cases (y = x) <;> simp_all

theorem preservation1_state : ∀ { Γ } { c c' : Com } { s s' },
  (Γ ⊢ c) -> (Γ ⊧ s) -> ((c, s) ~~> (c', s')) -> (Γ ⊧ s')
  := by
  intros Γ c c' s s' ty_c wf_s step_c_c'
  induction ty_c generalizing c' s <;> cases step_c_c' <;> repeat trivial
  . case Ty_Assign.Assign => apply update_ty; trivial; apply arith_preservation; repeat trivial
  . case Ty_Seq.Seq2      => rename_i ih1 _ _ _; apply ih1; repeat trivial


/- @@@
#### Commands: Progress

Progress requires using the `arith_progress` and `bool_progress`.
@@@ -/


theorem progress1 : ∀ { Γ s } { c : Com},
  (Γ ⊧ s) -> (Γ ⊢ c) ->  ¬ (c = Skip) -> ∃ c' s', (c, s) ~~> (c', s')
  := by
  intros Γ s c wf_s ty_c not_skip
  induction ty_c <;> repeat trivial
  . case Ty_Assign x a a_ty =>
    cases (arith_progress wf_s a_ty)
    repeat constructor
    repeat assumption
  . case Ty_Seq    =>
    rename_i c1 c2 c1_ty c2_ty ih1 ih2
    by_cases (c1 = Skip)
    . case pos =>
      apply Exists.intro; apply Exists.intro
      simp_all
      apply Step.Seq1
    . case neg c1_notskip =>
      cases (ih1 c1_notskip)
      rename_i c1' step1'
      cases step1'
      apply Exists.intro; apply Exists.intro;
      apply Step.Seq2
      repeat trivial
  . case Ty_If     =>
    rename_i b c1 c2 b_ty _ _ _ _
    cases (bool_progress wf_s b_ty)
    rename_i bv hbv
    cases bv
    . case intro.false =>
      apply Exists.intro; apply Exists.intro;
      apply Step.IfFalse; assumption
    . case intro.true =>
      apply Exists.intro; apply Exists.intro;
      apply Step.IfTrue; assumption
  . case Ty_While =>
    apply Exists.intro; apply Exists.intro;
    apply Step.While


/- @@@
#### Commands: Multiple Steps!

We would like to say something not just about a *single* step but about *all* the configurations
that may be reached by zero or more *steps*.

@@@ -/


abbrev Steps := star Step

notation:12 cs "~~>*" cs' => Steps cs cs'

/- @@@

Lets try to work out what preservation and progress look like for *many* steps.

**Preservation**

If the program does something THEN that thing is *expected* or *predicted*

```
∀ { c } ,

  __________________________________________ ->

  __________________________________________
```


**Progress** The program *does* something.

```
∀ { c } ,

  __________________________________________ ->

  __________________________________________
```

@@@ -/

theorem progress : ∀ { Γ } { c c' : Com } { s s' : State},
  (Γ ⊧ s) -> (Γ ⊢ c) -> ((c, s) ~~>* (c', s')) -> ¬ (c' = Skip) ->
  ∃ c'' s'', (c', s') ~~> (c'', s'')
  := by
  intros Γ c c' s s' wf_s ty_c steps not_skip
  generalize h : (c, s)   = cs at steps --- this is ANF / Nico's tip
  generalize h : (c', s') = cs' at steps --- this is ANF / Nico's tip
  induction steps generalizing Γ c s c' s'
  . case refl =>
    rename_i h1
    cases h1
    cases h
    apply (progress1 wf_s ty_c not_skip)
  . case step =>
    rename_i cs1 cs2 cs3 step1 step_rest ih hh
    cases cs2
    rename_i c2 s2
    cases h
    cases hh
    have ty_c2 : HasTyC Γ c2 := by apply (preservation1_com wf_s ty_c step1)
    have wf_s2 : Wf Γ s2     := by apply (preservation1_state ty_c wf_s step1)
    apply (ih wf_s2 ty_c2 not_skip)
    repeat trivial
