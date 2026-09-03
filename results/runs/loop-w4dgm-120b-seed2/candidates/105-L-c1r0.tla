---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

VARIABLES p

vars == <<p>>

Init == p = One

Halve == p' = [num |-> p.num, den |-> p.den * 2]

Normalize == p' = Norm(p)

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

====