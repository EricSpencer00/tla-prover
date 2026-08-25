---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS
  ArithmeticModules,
  ArithmeticOps,
  EqualityOps,
  ExtendsModules,
  FunctionApplication,
  IfThenElse,
  OperatorDefNames,
  RecordAccess,
  RecordConstructor,
  Specification,
  id

(* meta‑information constants *)
ArithmeticModules == {"Integers"}
ArithmeticOps == {"*", "\\div", "%"}
EqualityOps == {"="}
ExtendsModules == {"Integers"}
FunctionApplication == {"Norm([num |-> p.num \\div 2, den |-> p.den \\div 2])"}
IfThenElse == {"IF p.num % 2 = 0 /\\ p.den % 2 = 0 THEN Norm([num |-> p.num \\div 2, den |-> p.den \\div 2]) ELSE p (in Norm)"}
OperatorDefNames == {"One", "Half", "Norm"}
RecordAccess == {"p.num", "p.den"}
RecordConstructor == {"[num |-> 1, den |-> 1]", "[num |-> p.num, den |-> p.den * 2]", "[num |-> p.num \\div 2, den |-> p.den \\div 2]"}
Specification == "Dyadic rationals with normalization"
id == 105

(* ---------------------------------------------------------------------- *)
(* Dyadic rational definition: numerator is an integer, denominator a positive
   power of two. *)
IsPowerOfTwo(d) == \E k \in Nat : d = 2 ^ k

Dyadic == [num : Int, den : Nat] /\ den > 0 /\ IsPowerOfTwo(den)

(* ---------------------------------------------------------------------- *)
(* Operators required by the description *)

One == [num |-> 1, den |-> 1]

Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

Norm(p) ==
  IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

(* ---------------------------------------------------------------------- *)
(* Standard specification operators – trivially defined *)

SPECIFICATION == TRUE
INIT == TRUE
NEXT == UNCHANGED << >>
INVARIANTS == TRUE
PROPERTIES == TRUE

====