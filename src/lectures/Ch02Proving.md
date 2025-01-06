```lean
set_option pp.fieldNotation false

namespace MyBool

inductive Bool where
  | tt
  | ff
  deriving Repr

open Bool

def and(b1 b2: Bool) : Bool :=
  match b1, b2 with
  | tt, tt => tt
  | _, _   => ff

def or (b1 b2: Bool) : Bool :=
  match b1, b2 with
  | ff, ff => ff
  | _, _   => tt

-- exercise
theorem conj_comm : ∀ (b1 b2 : Bool), and b1 b2 = and b2 b1 := by
  intros b1 b2
  cases b1 <;> cases b2 <;> rfl

-- exercise
theorem or_comm : ∀ (b1 b2 : Bool), or b1 b2 = or b2 b1 := by
  intros b1 b2
  cases b1 <;> cases b2 <;> rfl


end MyBool


namespace MyNat

inductive Nat where
  | zero : Nat
  | succ : Nat -> Nat
  deriving Repr

open Nat

def n0 : Nat := zero
def n1 : Nat := succ zero
def n2 : Nat := succ (succ zero)
def n3 : Nat := succ (succ (succ zero))

def add (n m: Nat) : Nat :=
  match n with
  | zero => m
  | succ n' => succ (add n' m)

example : add n1 n2 = n3 := by rfl

theorem add_zero (n: Nat) : add n zero = n := by
  induction n
  . case zero => rfl
  . case succ => simp [add, *]


end MyNat

namespace MyList

inductive List (α : Type) where
  | nil : List α
  | cons : α -> List α -> List α
  deriving Repr

open List

def list0123 := cons 0 (cons 1 (cons 2 (cons 3 nil)))
def list3210 := cons 3 (cons 2 (cons 1 (cons 0 nil)))

def app {α : Type} (xs ys: List α) : List α :=
  match xs with
  | nil => ys
  | cons x xs' => cons x (app xs' ys)

example : app (cons 0 (cons 1 nil)) (cons 2 (cons 3 nil)) = list0123 := by
  simp [app, list0123]

def singleton {α : Type} (x: α) : List α := cons x nil

def rev {α : Type} (xs: List α) : List α :=
  match xs with
  | nil => nil
  | cons x xs' => app (rev xs') (singleton x)

example : rev list0123 = list3210 := rfl

example : app (cons 0 (cons 1 nil)) (cons 2 (cons 3 nil)) = cons 0 (cons 1 (cons 2 (cons 3 nil))) := rfl

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


def length {α : Type} (xs: List α) : Nat :=
  match xs with
  | nil => 0
  | cons _ xs' => 1 + length xs'

def pos_length (xs: List Nat) : Nat :=
  match xs with
  | nil => 0
  | cons x xs' => if x = 1 then length xs' + x else length xs'

theorem pos_len: ∀ (xs : List Nat), pos_length xs <= length xs := by
  intros xs
  induction xs
  case nil  => simp [pos_length]
  case cons x xs' _ =>
    simp [pos_length, length]
    split
    . simp [*, Nat.add_comm]
    . simp []


def count (k : Nat) (xs: List Nat) : Nat :=
  match xs with
  | nil => 0
  | cons x xs => if x = k then 1 + count k xs else count k xs

theorem count_length : ∀ (k : Nat) (xs : List Nat), count k xs <= length xs := by
  intros k xs
  induction xs
  case nil => simp [count]
  case cons x xs' ih =>
    simp [count, length]
    split
    . simp [*]
    . calc
        count k xs' <= length xs'     := by simp [*]
        _           <= length xs' + 1 := by simp []
        _           = 1 + length xs'  := by simp [Nat.add_comm]


def snoc {α : Type} (xs: List α) (y: α) : List α :=
  match xs with
  | nil => singleton y
  | cons x xs => cons x (snoc xs y)

def rev' {α : Type} (xs: List α) : List α :=
  match xs with
  | nil => nil
  | cons x xs => snoc (rev' xs) x

example : rev' (cons 1 (cons 2 (cons 3 nil))) = cons 3 (cons 2 (cons 1 nil)) := rfl

theorem rev_snoc_snoc : ∀ {α : Type} (xs: List α) (y: α), rev' (snoc xs y) = cons y (rev' xs) := by
  intros α xs y
  induction xs
  case nil => rfl
  case cons x xs ih => simp [snoc, rev', ih]

theorem rev_rev_snoc : ∀ {α : Type} (xs: List α), rev' (rev' xs) = xs := by
  intros α xs
  induction xs
  case nil => rfl
  case cons x xs ih => simp [rev', rev_snoc_snoc, ih]


def sum_to (n: Nat) : Nat :=
  match n with
  | 0           => 0
  | Nat.succ n' => n + sum_to n'

theorem sum_to_eq : ∀ (n : Nat), 2 * sum_to n = n * (n + 1) := by
  intros n
  induction n
  case zero => rfl
  case succ => simp_arith [*, sum_to, Nat.mul_add, Nat.mul_comm]

end MyList

section Tree

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α -> α -> Tree α -> Tree α
  deriving Repr

open Tree

def mirror {α : Type} (t: Tree α) : Tree α :=
  match t with
  | leaf => leaf
  | node l x r => node (mirror r) x (mirror l)

theorem mirror_mirror : ∀ {α : Type} (t: Tree α), mirror (mirror t) = t := by
  intros α t
  induction t
  case leaf => rfl
  case node => simp [mirror, *]

end Tree


namespace section_2_3

open Nat

#eval 2 + 3
#eval 1 - 10

def div2 (n: Nat) : Nat :=
  match n with
  | zero => zero
  | succ zero => zero
  | succ (succ n') => succ (div2 n')

theorem div2_thm : ∀ (n: Nat), div2 (n + n) = n := by
  intros n
  induction n
  case zero => rfl
  case succ n' ih =>
    calc
      div2 (n' + 1 + (n' + 1)) = div2 (((n' + n') + 1) + 1) := by simp_arith []
      _                        = div2 (n' + n') + 1         := by simp [div2]
      _                        = n' + 1                     := by simp [ih]

open List

-- literals
example : [1,2,3] = cons 1 (cons 2 (cons 3 nil)) := by rfl

-- nil
example : ([] : List Nat) = (nil : List Nat) := by rfl

-- cons
example : 1 :: [2,3] = cons 1 (cons 2 (cons 3 nil)) := by rfl

-- append
example : [1,2,3] ++ [4,5,6] = [1,2,3,4,5,6] := by rfl


open Tree
--- NEXT: 2.6
def contents {α : Type} (t: Tree α) : List α :=
  match t with
  | leaf => nil
  | node l x r => contents l ++ cons x (contents r)

def sum_tree (t: Tree Nat) : Nat :=
  match t with
  | leaf => 0
  | node l x r => sum_tree l + x + sum_tree r

def sum_list (l : List Nat) : Nat :=
  match l with
  | nil => 0
  | cons x xs => x + sum_list xs

theorem sum_list_append : ∀ (l1 l2 : List Nat), sum_list (l1 ++ l2) = sum_list l1 + sum_list l2 := by
  intros l1 l2
  induction l1
  case nil => simp [sum_list]
  case cons x xs ih => simp_arith [sum_list, *]

theorem sum_tree_eq : ∀ (t: Tree Nat), sum_tree t = sum_list (contents t) := by
  intros t
  induction t
  case leaf => rfl
  case node l x r _ _ => simp_arith [sum_tree, contents, sum_list, sum_list_append, *]

def preorder {α : Type} (t: Tree α) : List α :=
  match t with
  | leaf => nil
  | node l x r => cons x (preorder l ++ preorder r)

def postorder {α : Type} (t: Tree α) : List α :=
  match t with
  | leaf => nil
  | node l x r => postorder l ++ postorder r ++ cons x nil

theorem mirror_order : ∀ {α : Type} (t: Tree α), preorder (mirror t) = reverse (postorder t) := by
  intros α t
  induction t
  case leaf => rfl
  case node l x r _ _ => simp [mirror, preorder, postorder, *]

def map {α β : Type} (f: α -> β) : List α -> List β
  | [] => []
  | cons x xs => cons (f x) (map f xs)

def intersperse {α : Type} (y: α) (xs : List α) : List α :=
  match xs with
  | [] => []
  | cons x [] => cons x []
  | cons x xs' => cons x (cons y (intersperse y xs'))

#eval intersperse 0 [1,2,3]

theorem map_intersperse : (∀ {α β : Type} (f: α -> β) (y: α) (xs: List α), map f (intersperse y xs) = intersperse (f y) (map f xs)) := by
  intros α β f y xs
  induction xs
  case nil => rfl
  case cons x xs ih =>
    cases xs
    case nil => rfl
    case cons x' xs' => simp [intersperse, map, *]

-- NEXT: section 2.4
def rev {α : Type} (xs: List α) : List α :=
  match xs with
  | [] => []
  | cons x xs' => rev xs' ++ [x]


def itrev {α : Type} (xs ys: List α) : List α :=
  match xs with
  | [] => ys
  | cons x xs' => itrev xs' (cons x ys)

/- with explicit "generalizing"
theorem itrev_app' {α : Type} (xs ys: List α) : itrev xs ys = (rev xs) ++ ys :=
  match xs with
  | [] => rfl
  | cons x xs' => by simp [itrev, rev, itrev_app']
-/

theorem itrev_app : ∀ {α : Type} (xs ys: List α), itrev xs ys = (rev xs) ++ ys := by
  intros α xs ys
  induction xs generalizing ys
  case nil => rfl
  case cons x xs' ih => simp [itrev, rev, ih]

theorem itrev_nil : ∀ {α : Type} (ys: List α), itrev ys [] = rev ys := by
  intros α ys
  simp [itrev_app]


def itadd (n m: Nat) : Nat :=
  match n with
  | 0 => m
  | succ n' => itadd n' (succ m)

theorem itadd_eq : ∀ (n m: Nat), itadd n m = n + m := by
  intros n m
  induction n generalizing m
  case zero => simp [itadd]
  case succ n' ih => simp_arith [itadd, *]

-- NEXT: ex 2.10 [skip]

-- EX: 2.11 (***)
inductive Exp where
 | Var : Exp
 | Con : Nat -> Exp
 | Add : Exp -> Exp -> Exp
 | Mul : Exp -> Exp -> Exp
 deriving Repr

def eval (e: Exp) (x: Nat) : Nat :=
  match e with
  | Exp.Var       => x
  | Exp.Con n     => n
  | Exp.Add e1 e2 => eval e1 x + eval e2 x
  | Exp.Mul e1 e2 => eval e1 x * eval e2 x

abbrev Poly := List Nat

def evalp (p: Poly) (x: Nat) : Nat :=
  match p with
  | [] => 0
  | c::cs => c + x * (evalp cs x)

def addp (p1 p2: Poly) : Poly :=
  match p1, p2 with
  | [], _ => p2
  | _, [] => p1
  | c1::cs1, c2::cs2 => (c1 + c2) :: addp cs1 cs2

theorem add_poly : ∀ (p q : Poly) (x: Nat), evalp (addp p q) x = evalp p x + evalp q x := by
  intros p q x
  induction p, q using addp.induct
  case case1 p2 => simp_arith [addp, evalp]
  case case2 p1 _ => simp_arith [addp, evalp]
  case case3 c1 cs1 c2 cs2 _ => simp_arith [addp, evalp, Nat.mul_add, *]


theorem zero_poly : ∀ (p : Poly) (x: Nat), evalp (0 :: p) x = x * (evalp p x)  := by
  intros p x
  simp_arith [evalp]

def mulc (k: Nat) (p: Poly) : Poly :=
  match p with
  | []    => []
  | c::cs => k * c :: mulc k cs

theorem mulc_poly : ∀ (k: Nat) (p: Poly) (x: Nat), evalp (mulc k p) x = k * evalp p x := by
  intros k p x
  induction p
  case nil => rfl
  case cons c cs ih => simp_arith [mulc, evalp, Nat.mul_add, *]
                       calc
                         x * (k * evalp cs x) = (x * k) * (evalp cs x) := by simp [Nat.mul_assoc]
                         _                    = (k * x) * (evalp cs x) := by simp [Nat.mul_comm]
                         _                    = k * (x * evalp cs x)   := by simp [Nat.mul_assoc]

def mulp (p q: Poly) : Poly :=
  match p with
  | []    => []
  | c::p' => addp (mulc c q) (0 :: mulp p' q)

theorem mul_poly : ∀ (p q : Poly) (x: Nat), evalp (mulp p q) x = evalp p x * evalp q x := by
  intros p q x
  induction p
  case nil => simp_arith [mulp, evalp]
  case cons c p ih => simp_arith [mulp, evalp, add_poly, mulc_poly, *, Nat.add_mul, Nat.mul_assoc]

def coeffs (e: Exp) : Poly :=
  match e with
  | Exp.Var => [0, 1]
  | Exp.Con n => [n]
  | Exp.Add e1 e2 => addp (coeffs e1) (coeffs e2)
  | Exp.Mul e1 e2 => mulp (coeffs e1) (coeffs e2)

theorem eval_poly : ∀ (e:Exp) (x:Nat), evalp (coeffs e) x = eval e x := by
  intros e x
  induction e
  case Var => simp [coeffs, evalp, eval]
  case Con n => rfl
  case Add e1 e2 ih1 ih2 => simp_arith [coeffs, eval, add_poly, * ]
  case Mul e1 e2 ih1 ih2 => simp_arith [coeffs, eval, mul_poly, * ]
end section_2_3

namespace section_4_5

open Bool
open Nat

inductive ev : Nat -> Prop where
  | ev0 : ev 0
  | evSS : ∀ {n: Nat}, ev n -> ev (n + 2)

open ev

def even (n: Nat) : Bool :=
  match n with
  | 0 => true
  | 1 => false
  | succ (succ n) => even n

def even_4 : ev 4 := evSS (evSS ev0)

def even_6 : ev 6 := evSS (even_4)

def even_8 : ev 8 := by
  apply evSS
  apply evSS
  apply evSS
  apply evSS
  apply ev0

theorem ev_even : ∀ (n : Nat), ev n -> even n = true := by
  intros n h
  induction h
  case ev0  => rfl
  case evSS => simp [even, *]

theorem even_ev : ∀ (n : Nat), even n = true -> ev n := by
  intros n h
  induction n using even.induct
  case case1 => apply ev0
  case case2 => contradiction
  case case3 => simp_all [even, evSS]

inductive star {α : Type} (r: α -> α -> Prop) : α -> α -> Prop where
  | refl : ∀ {a : α}, star r a a
  | step : ∀ {a b c : α}, r a b -> star r b c -> star r a c

open star

theorem star_trans {α : Type} {r : α -> α -> Prop} : ∀ {a b c : α}, star r a b -> star r b c -> star r a c := by
  intros a b c star_ab star_bc
  induction star_ab
  case _ => apply star_bc -- or assumption
  case step a x b r_ax _ ih => simp_all [step r_ax] -- apply step r_ax (ih star_bc)

-- theorem star_trans' {α : Type} {r : α -> α -> Prop} {a b c : α} (star_ab : star r a b) (star_bc : star r b c) : star r a c :=
--     match star_ab with
--     | refl => star_bc
--     | step r_ax star_xb => step r_ax (star_trans' star_xb star_bc)

-- by
--   intros a b c star_ab star_bc
--   induction star_ab
--   case _ => apply star_bc -- or assumption
--   case step a x b r_ax _ ih => apply step r_ax (ih star_bc)

def rev {α : Type} (xs: List α) : List α :=
  match xs with
  | [] => []
  | x :: xs' => (rev xs') ++ [x]

inductive palindrome : List Nat -> Prop where
  | emp : palindrome []
  | sng : ∀ (n : Nat), palindrome [n]
  | cns : ∀ (n : Nat) (ns : List Nat), palindrome ns -> palindrome (n :: ns ++ [n])

theorem rev_app : ∀ {α: Type} (xs ys : List α), rev (xs ++ ys) = rev ys ++ rev xs := by
  intros _ xs ys
  induction xs
  case nil => simp [rev]
  case cons => simp [rev, *]

theorem palindrome_rev : ∀ (ns : List Nat), (palindrome ns) -> rev ns = ns := by
  intros ns pal_ns
  induction pal_ns
  case emp => simp [rev]
  case sng => simp [rev]
  case cns n ns' _ ih => simp [rev, rev_app, *]

inductive iter {α : Type} (r : α -> α -> Prop) : Nat -> α -> α -> Prop where
  | iter_base : ∀ {a : α}, iter r 0 a a
  | iter_step : ∀ {n : Nat} {a b c : α}, r a b -> iter r n b c -> iter r (succ n) a c

theorem star_one : ∀ { α : Type} { r: α -> α -> Prop} {a b : α}, r a b -> star r a b := by
  intros α r a b r_ab
  apply step r_ab
  apply refl

theorem star_iter : ∀ {α : Type} {r : α -> α -> Prop} {a b : α}, star r a b -> ∃ (n : Nat), iter r n a b := by
  intros α r a b star_ab
  induction star_ab
  case refl => exists 0; constructor
  case step x b c r_ab star_bc iter_n_bc =>
    cases iter_n_bc
    . case intro n bc => exists (n+1); constructor <;> assumption

inductive Alphabet where
  | a : Alphabet
  | b : Alphabet
  deriving Repr

open Alphabet

inductive gS : List Alphabet -> Prop where
   | gS0 : gS []
   | gS1 : ∀ {s : List Alphabet}, gS s -> gS (a :: s ++ [b])
   | gS2 : ∀ {s1 s2 : List Alphabet}, gS s1 -> gS s2 -> gS (s1 ++ s2)

inductive gT : List Alphabet -> Prop where
  | gT0 : gT []
  | gT1 : ∀ {t1 t2 : List Alphabet}, gT t1 -> gT t2 -> gT (t1 ++ ([a] ++ t2 ++ [b]))

open gS
open gT

theorem T_append : ∀ {s1 s2 : List Alphabet}, gT s1 -> gT s2 -> gT (s1 ++ s2) := by
  intros s1 s2 T_s1 T_s2
  induction T_s2
  case gT0 => simp [List.append_nil]; assumption
  case gT1 t1' t2' _ _ _ _ =>
    have h : (s1 ++ (t1' ++ ([a] ++ t2' ++ [b]))) = (s1 ++ t1' ++ ([a] ++ t2' ++ [b])) := by simp [List.append_assoc]
    rw [h]
    constructor
    assumption
    assumption

theorem S_imp_T : ∀ {w : List Alphabet}, gS w -> gT w := by
  intros _ gs
  induction gs
  case gS0 => constructor
  case gS1 => apply (gT1 gT0); assumption
  case gS2 _ s1 s2 _ _ T_s1 T_s2 => apply T_append <;> assumption

theorem T_imp_S : ∀ {w : List Alphabet}, gT w -> gS w := by
  intros _ gt
  induction gt
  case gT0 => constructor
  case gT1 => constructor
              . case _ => assumption
              . case _ => constructor
                          simp [List.append]
                          assumption

end section_4_5


inductive Tree0 where
  | L0 : Tree0
  | N0 : Tree0 -> Tree0 -> Tree0

open Tree0

def nodes(t:Tree0) : Nat :=
  match t with
  | L0 => 0
  | N0 l r => 1 + nodes l + nodes r

def explode (n:Nat) (t: Tree0) : Tree0 :=
  match n with
  | 0      => t
  | n' + 1 => explode n' (N0 t t)

def t0 := L0

-- theorem explode_nodes_size :nodes (explode n t) = 2^n * (nodes t) + 2^n - 1 := by
--   induction n generalizing t
--   .case zero =>
--    simp_all [nodes, explode]
--   .case succ n' ih =>
--    simp_all [nodes, explode]
--    generalize bob : nodes t = k
--    generalize foo :  2 ^ n' * (1 + k + k) + 2 ^ n' - 1 = lhs
--    generalize bar : 2 ^ (n' + 1) * k + 2 ^ (n' + 1) - 1 = rhs
--    have h1 : lhs = (2 ^ (n' + 1) * ( k + 1)) - 1 :=
--      calc lhs
--        _ = 2 ^ n' * (1 + k + k) + 2 ^ n' - 1 := by simp_all
--        _ = 2 ^ n' * (1 + 2 * k) + 2 ^ n' - 1 := by sorry
--        _ = 2 ^ n' * (2 * k + 1) + 2 ^ n' - 1 := by sorry
--        _ = 2 ^ n' * (2 * k + 2)          - 1 := by sorry
--        _ = 2 ^ n' * (2 * (k + 1))        - 1 := by sorry
--        _ = 2 ^ (n' + 1) * (k + 1) - 1        := by sorry

--    have h2 : rhs = (2 ^ (n' + 1) * ( k + 1)) - 1 := by
--     sorry
--    simp_all []

#eval nodes (explode 0 t0) -- 0
#eval nodes (explode 1 t0) -- 1
#eval nodes (explode 2 t0) -- 3
#eval nodes (explode 3 t0) -- 7
#eval nodes (explode 4 t0) -- 15
#eval nodes (explode 5 t0) -- 31

-- nodes (explode n t) =  n ... (nodes t)
```

