---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS Operands

ArithmeticModules == {"Integers"}
ArithmeticOps == {"*", "\div", "%"}
EqualityOps == {"="}
ExtendsModules == {"Integers"}
FunctionApplication == {"Norm([num |-> p.num \div 2, den |-> p.den \div 2])"}
IfThenElse == {"IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p (in Norm)"}
OperatorDefNames == {"One", "Half", "Norm"}
RecordAccess == {"p.num", "p.den"}
RecordConstructor == {"[num |-> 1, den |-> 1]", "[num |-> p.num, den |-> p.den * 2]", "[num |-> p.num \div 2, den |-> p.den \div 2]"}

VARIABLES p

Spec == p \in [num : Operands, den : Operands]

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Init == p = One

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Halve == p' = Half

Normalize == p' = Norm(p)

Next == Halve \/ Normalize

InitSpec == Init /\ [][Next]_p

StateConstraint == Spec

VariableStarvation == (p.den # 1) ~> (p.den = 1)

====