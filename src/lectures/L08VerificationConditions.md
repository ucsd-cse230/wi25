```lean
import Cse230wi25.BigStep
import Cse230wi25.L07Axiomatic

set_option pp.fieldNotation false
set_option pp.proofs true
```


# Automating Floyd-Hoare with Verification Conditions

FH rules are nice but still *quite* tedious to use, because it seems like we
need to spell out

1. where to apply which rule
2. how exactly the rules of consequence work

etc.

In fact, the rules are *mostly* **syntax directed** meaning that there is
**exactly one** rule that can be applied for each kind of term.

- The rules of _consequence_
- The loop _invariant_

Next, lets see how we can automate away more or less everything except
the above.



## Annotated Commands

Lets assume that the programmer has **annotated** their code with the
loop invariant, so we can define a `ACom` type which looks just like
the previous `Com` except for the loop constructor which is now of the
form `While inv b c` case, so the `inv` is baked into the code.



```lean
inductive ACom where
  | Skip   : ACom
  | Assign : Vname -> Aexp -> ACom
  | Seq    : ACom  -> ACom -> ACom
  | If     : Bexp  -> ACom -> ACom -> ACom
  | While  : Assertion -> Bexp  -> ACom -> ACom

open ACom
```

In fact, if we `erase` the `inv` from each while, we can convert an `ACom` program
back into the old `Com` programs.

```lean
@[simp]
def erase (c : ACom) : Com :=
  match c with
  | ACom.Skip        => Com.Skip
  | ACom.Assign x a  => Com.Assign x a
  | ACom.Seq c1 c2   => Com.Seq     (erase c1) (erase c2)
  | ACom.If b c1 c2  => Com.If b    (erase c1) (erase c2)
  | ACom.While _ b c => Com.While b (erase c)
```

As before we can define some "notation" to make it easier to write `ACom` programs.

  |- {λ s => inv s /\ bval b s} c {λs => inv s}

One lean-y way to say that `inv` is an invariant:

∀ {s, t},
  ⟨ c , s ⟩ ==> t ->
  inv s ->
  bval b s ->
  inv t

wp : Com -> Assertion -> Assertion

{λ s => inv s /\ bval b s} ⊆ wp c inv



```lean
notation:10 x "<~" e  => ACom.Assign x (ToAexp.toAexp e)
infixr:20 ";;"  => ACom.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => ACom.If b c1 c2
notation:12 "WHILE {-@" inv "@-}" b "DO" c "END" => ACom.While inv (ToBexp.toBexp b) c
notation:20 "[|" c "|]" => erase c
notation:10 "⊢" " {|" p "|}" c "{|" q "|}" => FH p (erase c) q

-- REPEAT c UNTIL b == c ;; WHILE (not c) DO c END
```



Specifically, note the `⊢ {| p |} c {| q |}` triple
which means that the triple holds for the **erased**
command `c`.

## Weakest Preconditions

The central idea is reformulate the FH rules into the notion
of the **weakest precondition** `wp c q` which defines the
**largest** set of *starting states* from which executing
the command `c` will yield a *final state* in which the
assertion `q` is guaranteed to hold.


```lean
@[simp]
def wp (c: ACom) (q : Assertion) : Assertion :=
  match c with
  | ACom.Skip        => q
  | ACom.Assign x a  => q [[ x := a ]]
  | ACom.Seq c1 c2   => wp c1 (wp c2 q)
  | ACom.If b c1 c2  => (λ s => if bval b s then wp c1 q s else wp c2 q s)
  | ACom.While i _ _ => i

@[simp]
def vc (c : ACom) (q : Assertion) : Prop :=
  match c with
  | ACom.Skip        => True
  | ACom.Assign _ _  => True
  | ACom.Seq c1 c2   => vc c1 (wp c2 q) /\ (vc c2 q)
  | ACom.If _ c1 c2  => vc c1 q /\ vc c2 q
  | ACom.While i b c =>
                        -- ((λ s => i s /\ bval b s) ⊆ (wp c i)) /\
                        (∀ s, i s -> bval b s -> wp c i s) /\
                        (∀ s, i s -> ¬ bval b s -> q s) /\
                        vc c i

theorem vc_sound : vc c q -> (⊢ {| wp c q |} c {| q |})
  := by
  intros vcq
  induction c generalizing q
  . case Skip   => constructor
  . case Assign => constructor
  . case Seq    =>
    rename_i c1 c2 ih1 ih2
    simp [vc] at vcq
    cases vcq
    simp []
    constructor
    apply ih1
    assumption
    apply ih2
    assumption
  . case If     => sorry
  . case While  => sorry

/- ----------------------------------------------------------------------------------------------- -/

@[simp]
def vc' (p: Assertion) (c: ACom) (q: Assertion) : Prop := (p ⊆ wp c q) ∧ (vc c q)

theorem vc'_sound : (vc' p c q) -> (⊢ {| p |} c {| q |}) := by
  intros vcq
  cases vcq
  rename_i vc1 vc2
  apply FH.CnsL
  apply vc_sound; assumption
  apply vc1


/- ----------------------------------------------------------------------------------------------- -/

theorem ex_swap : ∀ {a b},
  ⊢ {| λs => s x = a /\ s y = b |}
      (z <~ x) ;;
      (x <~ y) ;;
      (y <~ z)
    {| λs => s x = b /\ s y = a |}
  := by
  intros a b
  apply vc'_sound
  simp [vc', aval, upd]
  intros; constructor <;> assumption

/- ----------------------------------------------------------------------------------------------- -/

theorem ex1 :
  ⊢ {| tt |}
    x <~ 5
    {| λs => s x = 5 |}
  := by
  apply vc'_sound
  simp_all [aval, upd]

/- ----------------------------------------------------------------------------------------------- -/

theorem ex2 :
  ⊢ {| λs => s x = 10 /\ s y = 1 |}  -- (2) ??
      (x <~ x + y) ;;
      (x <~ x + y)
    {| λs => s x = 12 |}  -- (1) ??
  := by
  apply vc'_sound; simp_all [aval, upd]

-- (1) change POST to λ s => s x = 12 /\ s y = 1
-- (2) change PRE  to λ s => s x = 10 /\ s y = 1

/- ----------------------------------------------------------------------------------------------- -/


theorem ex4 :
  ⊢ {| tt |}
    WHILE {-@ tt @-} true DO
      Skip
    END
    {| ff |}
  := by
  apply vc'_sound
  simp [vc', bval]

/-
vc' tt (while {tt} true skip) ff
==
vc (while {tt} true skip) ff

-- (1) tt /\ true => (wp Skip inv)
-- (2) tt /\ not true => ff

-/
  -- simp_all [aval, bval]

/- ----------------------------------------------------------------------------------------------- -/

-- x=100, 100+0, 100+0+1, 100+0+1+2, 100+0+1+2+3,... 100+0+1+2+3+...+(z-1)

theorem ex_loop :
  ⊢ {| tt |}
      (y <~ 0)   ;;
      (x <~ 100) ;;
      (WHILE {-@ λs => 100 <= s x  @-} y << z DO
         ((x <~ x + y) ;;
          (y <~ y + 1))
      END)
    {| λ s => 100 <= s x |}
  := by
  apply vc'_sound
  simp [bval, aval, upd]
  constructor
  . intros s x_100 _
    calc 100 <= s x       := by assumption
         _   <= s x + s y := by simp []
  . intros; assumption


/-
(x:=n, y:=0)
(x:=n-1, y := 1)
(x:=n-2, y := 2)
(x:=n-3, y := 3)
...
(x:=1,   y := n-1)
(x:=0,   y := n)


(x:=0,   y := n)
-/

theorem bob : ∀ {a b}, 0 < a -> a - 1 + (b + 1) = a + b := by
  intros a b a_pos

  cases a
  . contradiction
  . simp_arith []

theorem ex_drain: ∀ {n: Nat},
  ⊢ {| λ s => s x = n |}
      (y <~ 0)
      ;;
      (WHILE {-@ λ s => s x + s y = n @-} 0 << x DO
         ((x <~ x - 1) ;;
          (y <~ y + 1))
      END)
    {| λ s => s y = n |}
  := by
  intro n
  apply vc'_sound
  simp [bval, aval, upd]
  constructor
  . intros s xy_n x_pos; simp [<-xy_n]; apply bob; assumption
  . intros s xy_n x_0; simp_all[]

/-
x:=n, y:=0
x:=n-1, y:=0 +)
x:=n-2, y:=0 +n + (n-1)
x:=n-3, y:=0 +n + (n-1) +(n-2)
...
x:=0  , y:=0 +n + (n-1) +(n-2)+ ...+ 1


-/


theorem imp_sum' : ∀ {n},
  ⊢ {| λ s => s "x" = n |}
      (y <~ 0) ;;
      (WHILE {-@ λs => s y + sum (s x) = sum n @-} (0 << x) DO
        (y <~ y + x) ;;
        (x <~ x - 1)
       END)
    {| λ s => s "y" = sum n |}
  := by
  intros n
  apply vc'_sound
  simp_all [aval, bval, upd]
  constructor <;> repeat constructor
  . case a.left =>
    intros
    rename_i s a b
    generalize hx : s x = vx
    cases vx <;> simp_all [sum, Nat.add_assoc, Nat.add_comm]

  . case a.right =>
    intros
    rename_i s _ _
    generalize hx : s x = vx
    cases vx <;> simp_all [sum, Nat.add_assoc]
```

