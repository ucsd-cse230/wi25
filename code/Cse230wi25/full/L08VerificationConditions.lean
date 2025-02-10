import LeanConcreteSemantics.BigStep
import LeanConcreteSemantics.Ch12Axiomatic

import Smt

set_option pp.fieldNotation false
set_option pp.proofs true

inductive ACom where
  | Skip   : ACom
  | Assign : Vname -> Aexp -> ACom
  | Seq    : ACom  -> ACom -> ACom
  | If     : Bexp  -> ACom -> ACom -> ACom
  | While  : Assn -> Bexp  -> ACom -> ACom
open ACom

@[simp]
def pre (c: ACom) (q : Assn) : Assn :=
  match c with
  | ACom.Skip        => q
  | ACom.Assign x a  => ( q [[ x := a ]] )
  | ACom.Seq c1 c2   => pre c1 (pre c2 q)
  | ACom.If b c1 c2  => (λ s => if bval b s then pre c1 q s else pre c2 q s)
  | ACom.While i _ _ => i

@[simp]
def vc (c : ACom) (q : Assn) : Prop :=
  match c with
  | ACom.Skip        => True
  | ACom.Assign _ _  => True
  | ACom.Seq c1 c2   => vc c1 (pre c2 q) /\ (vc c2 q)
  | ACom.If _ c1 c2  => vc c1 q /\ vc c2 q
  | ACom.While i b c => (∀ s, i s -> bval b s -> pre c i s) /\
                        (∀ s, i s -> ¬ bval b s -> q s) /\
                        vc c i

@[simp]
def erase (c : ACom) : Com :=
  match c with
  | ACom.Skip        => Com.Skip
  | ACom.Assign x a  => Com.Assign x a
  | ACom.Seq c1 c2   => Com.Seq     (erase c1) (erase c2)
  | ACom.If b c1 c2  => Com.If b    (erase c1) (erase c2)
  | ACom.While _ b c => Com.While b (erase c)



theorem vc_sound : vc c q -> (⊢ {{ pre c q }} (erase c) {{ q }})
  := by
  intros vcq
  induction c generalizing q
  . case Skip   => constructor
  . case Assign => constructor
  . case Seq 	=> sorry
  . case If 	=> sorry 
  . case While 	=> sorry

/- ----------------------------------------------------------------------------------------------- -/

@[simp]
def vc' (p: Assn) (c: ACom) (q: Assn) : Prop := (p ⊆ pre c q) ∧ (vc c q)

theorem vc'_sound : vc' p c q -> (⊢ {{ p }} (erase c) {{ q }}) := by
  intros vcq
  cases vcq
  rename_i vc1 vc2
  apply FH.Cnsq
  apply vc1
  apply vc_sound; assumption
  apply implies_refl


/- ----------------------------------------------------------------------------------------------- -/
-- use `notation` for the below
notation:10 x "<~" e  => ACom.Assign x (ToAexp.toAexp e)
infixr:20 ";;"  => ACom.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => ACom.If b c1 c2
notation:12 "WHILE {-@" inv "@-}" b "DO" c "END" => ACom.While inv (ToBexp.toBexp b) c
notation:20 "[|" c "|]" => erase c
notation:10 "⊢" " {|" p "|}" c "{|" q "|}" => FH p (erase c) q

@[simp]
def tt : Assn := λ_ => True

@[simp]
def ff : Assn := λ_ => False

theorem ex1 : ⊢ {| tt |}
                  x <~ 5
                {| λs => s x = 5 |}
  := by
  apply vc'_sound; simp_all [aval, upd]

theorem ex2 : ⊢ {| λs => s x = 10 |}
                  (x <~ x + 1) ;;
                  (x <~ x + 1)
                {| λs => s x = 12 |}
  := by
  apply vc'_sound; simp_all [aval, upd]

theorem ex3 : ⊢ {| λs => s x = a /\ s y = b |}
                    (z <~ x) ;;
                    (x <~ y) ;;
                    (y <~ z)
                {| λs => s x = b /\ s y = a |}
  := by
  apply vc'_sound; simp_all [aval, upd]

theorem ex4 : ⊢ {| tt |}
                WHILE {-@ tt @-} true DO
                  Skip
                END
                {| ff |}
  := by
  apply vc'_sound
  simp_all [aval, bval]

theorem imp_sum' : ⊢ {| λ s => s "x" = i |}
                      (y <~ 0) ;;
                      (WHILE {-@ wsum_inv i @-} (0 << x) DO
                        (y <~ y + x) ;;
                        (x <~ x - 1)
                       END)
                      {| λ s => s "y" = sum i |}
  := by
  apply vc'_sound
  simp_all [aval, bval, wsum_inv, upd]
  apply And.intro <;> repeat (apply And.intro)
  . case a.left =>
    intros
    rename_i s _ _
    generalize hx : s x = vx
    cases vx <;> simp_all [sum, Nat.add_assoc]
  . case a.right =>
    intros
    rename_i s _ _
    generalize hx : s x = vx
    cases vx <;> simp_all [sum, Nat.add_assoc]

/- SMT stuff ------------------------------------------------------------------------------------- -/
example {U : Type} [Nonempty U] {f : U → U → U} {a b c d : U}
  (h0 : a = b) (h1 : c = d) (h2 : p1 ∧ True) (h3 : (¬ p1) ∨ (p2 ∧ p3))
  (h4 : (¬ p3) ∨ (¬ (f a c = f b d))) : False := by
  smt [h0, h1, h2, h3, h4]
