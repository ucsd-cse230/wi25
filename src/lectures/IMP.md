```lean
import Cse230wi25.States
import Cse230wi25.Expressions

set_option pp.fieldNotation false
set_option pp.proofs true

-- Commands ----------------------------------------------------------

inductive Com where
  | Skip   : Com
  | Assign : Vname -> Aexp -> Com
  | Seq    : Com   -> Com  -> Com
  | If     : Bexp  -> Com  -> Com -> Com
  | While  : Bexp  -> Com  -> Com
  deriving Repr

open Com

def bLess (a1 a2 : Aexp) : Bexp := Bexp.BLess a1 a2

infix:10 "<<"  => fun x y => Bexp.BLess (ToAexp.toAexp x) (ToAexp.toAexp y)
infix:10 "<~"  => Com.Assign
infixr:8 ";;"  => Com.Seq
notation:10 "IF" b "THEN" c1 "ELSE" c2 => Com.If b c1 c2
notation:12 "WHILE" b "DO" c "END" => Com.While b c

def com0 := "x" <~ "y" + 1
def com1 := "y" <~ 2
def com2 := com0 ;; com1
def com3 := x <~ y + 1 ;; y <~ x + 2
def com4 := Skip ;; Skip ;; Skip ;; Skip
def com5 := IF 10 << x THEN x <~ 1 ELSE y <~ 2
def com6 := WHILE x << 5 DO x <~ x + 1 END

def st_x_10_y_20 := st0 [x := 10 ] [ y := 20]

#eval com3
#eval com4
```

