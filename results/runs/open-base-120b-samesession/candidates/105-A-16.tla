---- MODULE DyadicRationals ----
EXTENDS Integers

(*--- meta-data identifiers ---*)
ArithmeticModules == {"Integers"}
ArithmeticOps == {"*", "\\div", "%"}
EqualityOps == {"="}
ExtendsModules == {"Integers"}
FunctionApplication == "Norm([num |-> p.num \\div 2, den |-> p.den \\div 2])"
IfThenElse == "IF p.num % 2 = 0 /\\ p.den % 2 = 0 THEN Norm([num |-> p.num \\div 2, den |-> p.den \\div 2]) ELSE p (in Norm)"
OperatorDefNames == {"One", "Half", "Norm"}
RecordAccess == {"p.num", "p.den"}
RecordConstructor == {"[num |-> 1, den |-> 1]",
                      "[num |-> p.num, den |-> p.den * 2]",
                      "[num |-> p.num \\div 2, den |-> p.den \\div 2]"}
id == 105

(*--- dyadic rational definition ---*)
Dyadic == { [num |-> n, den |-> d] : n \in Int /\ d \in Nat /\ d > 0 }

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
            THEN Norm([num |-> p.num \\div 2, den |-> p.den \\div 2])
            ELSE p

(*--- specification skeleton required by the task ---*)
SPECIFICATION == TRUE
INIT == TRUE
NEXT == TRUE
INVARIANTS == {}
PROPERTIES == {}

====