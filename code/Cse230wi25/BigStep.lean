import Cse230wi25.States
import Cse230wi25.IMP

open Com

-- inductive BigStep : Com -> State -> State -> Prop where
--   | Skip {st} :  BigStep Skip st st
--   | Assign {st a n} : BigStep (Assign a n) st (st [a := aval n st])
--   | Seq {c1 c2 st1 st2 st3} : BigStep c1 st1 st2 -> BigStep c2 st2 st3 -> BigStep (Seq c1 c2) st1 st3
--   | IfTrue {b c1 c2 st st'} : bval b st = true -> BigStep c1 st st' -> BigStep (If b c1 c2) st st'
--   | IfFalse {b c1 c2 st st'} : bval b st = false -> BigStep c2 st st' -> BigStep (If b c1 c2) st st'
--   | WhileFalse {b c st} : bval b st = false -> BigStep (While b c) st st
--   | WhileTrue {b c st st' st''} : bval b st = true -> BigStep c st st' -> BigStep (While b c) st' st'' -> BigStep (While b c) st st''

inductive BigStep : Com -> State -> State -> Prop where
  | Skip   : ∀ {st},
                BigStep Skip st st
  | Assign : ∀ {st a n},
                BigStep (Assign a n) st (st [a := aval n st])
  | Seq    : ∀ {c1 c2 st1 st2 st3},
                BigStep c1 st1 st2 -> BigStep c2 st2 st3 ->
                BigStep (Seq c1 c2) st1 st3
  | IfTrue : ∀ {b c1 c2 st st'},
                bval b st = true -> BigStep c1 st st' ->
                BigStep (If b c1 c2) st st'
  | IfFalse : ∀ {b c1 c2 st st'},
                bval b st = false -> BigStep c2 st st' ->
                BigStep (If b c1 c2) st st'
  | WhileFalse : ∀ {b c st},
                bval b st = false ->
                BigStep (While b c) st st
  | WhileTrue : ∀ {b c st st' st''},
                bval b st = true -> BigStep c st st' -> BigStep (While b c) st' st'' ->
                BigStep (While b c) st st''

notation:12 "⟨" c "," s "⟩ ==> " t  => BigStep c s t
