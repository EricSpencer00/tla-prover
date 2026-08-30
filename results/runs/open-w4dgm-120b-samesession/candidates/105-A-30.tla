---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(x) == IF x.num % 2 = 0 /\ x.den % 2 = 0 THEN Norm([num |-> x.num \div 2, den |-> x.den \div 2]) ELSE x

Init == p = One

Next == p' = Half

Spec == Init /\ [][Next]_p

====