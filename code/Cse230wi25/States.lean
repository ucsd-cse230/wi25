set_option pp.fieldNotation false
set_option pp.proofs true

-- Variables, Values and States -------------------------------
abbrev Val := Nat
abbrev Vname := String

abbrev State := Vname -> Val
-- update state
def upd (s: State) (x: Vname) (v: Val) : State :=
  λ y => if y = x then v else s y

notation:10 s " [ " x " := " v " ] " => upd s x v
