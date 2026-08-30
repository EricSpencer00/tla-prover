---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES val

vars == <<val>>

Init == val = One

Next == \E p \in {One, Half} : val' = Norm(p)

Spec == Init /\ [][Next]_vars

TypeOK == val \in {One, Half}

ValueIsDyadic == val.den = 2 ^ (val.num - 1)

====