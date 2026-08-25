---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANT ArithmeticModules
CONSTANT ArithmeticOps
CONSTANT EqualityOps
CONSTANT ExtendsModules
CONSTANT FunctionApplication
CONSTANT IfThenElse
CONSTANT ModuleName
CONSTANT OperatorDefNames
CONSTANT RecordAccess
CONSTANT RecordConstructor

(* values of the meta‑data constants *)
ArithmeticModules == {"Integers"}
ArithmeticOps == {"*", "\\div", "%"}
EqualityOps == {"="}
ExtendsModules == {"Integers"}
FunctionApplication == {"Norm([num |-> p.num \\div 2, den |-> p.den \\div 2])"}
IfThenElse == {"IF p.num % 2 = 0 /\\ p.den % 2 = 0 THEN Norm([num |-> p.num \\div 2, den |-> p.den \\div 2]) ELSE p (in Norm)"}
ModuleName == "DyadicRationals"
OperatorDefNames == {"One", "Half", "Norm"}
RecordAccess == {"p.num", "p.den"}
RecordConstructor == {"[num |-> 1, den |-> 1]", "[num |-> p.num, den |-> p.den * 2]", "[num |-> p.num \\div 2, den |-> p.den \\div 2]"}

(* dyadic rational operators *)
One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)
Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLE p

Init == p = One

Next == /\ p' \in { Half(p), Norm(p) }

(* required operators with exact names *)
INIT == Init
NEXT == Next
INVARIANTS == /\ p.den > 0 /\ p.den \in Int
PROPERTIES == TRUE

SPECIFICATION == Init /\ [][Next]_<<p>>

====