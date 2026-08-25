---- MODULE DyadicRationals ----
EXTENDS Integers

(* ----------------------------------------------------------------------
   Metadata (as required by the description)
   ---------------------------------------------------------------------- *)

ArithmeticModules == {"Integers"}
ArithmeticOps == {"*", "\div", "%"}
EqualityOps == {"="}
ExtendsModules == {"Integers"}
FunctionApplication == {"Norm([num |-> p.num \div 2, den |-> p.den \div 2])"}
IfThenElse == {"IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p (in Norm)"}
ModuleName == "DyadicRationals"
OperatorDefNames == {"One", "Half", "Norm"}
RecordAccess == {"p.num", "p.den"}
RecordConstructor == {
  "[num |-> 1, den |-> 1]",
  "[num |-> p.num, den |-> p.den * 2]",
  "[num |-> p.num \div 2, den |-> p.den \div 2]"
}
Specification == "Dyadic rational arithmetic with normalization"
id == 105

(* ----------------------------------------------------------------------
   Types
   ---------------------------------------------------------------------- *)

Dyadic == { p \in [num : Int, den : Nat] : p.den > 0 }

(* ----------------------------------------------------------------------
   Operators required by the specification
   ---------------------------------------------------------------------- *)

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) ==
  IF (p.num % 2 = 0) /\ (p.den % 2 = 0)
  THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
  ELSE p

(* ----------------------------------------------------------------------
   A tiny behavioural spec (optional – no .cfg identifiers required)
   ---------------------------------------------------------------------- *)

VARIABLE p

Init == p = One

Next ==
  \/ p' = Half(p)
  \/ p' = Norm(p)
  \/ UNCHANGED p

Spec == Init /\ [][Next]_p

Invariant == p \in Dyadic

Properties == TRUE

====