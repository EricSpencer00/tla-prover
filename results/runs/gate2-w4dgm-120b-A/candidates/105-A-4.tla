---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules,
          FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess,
          RecordConstructor, Specification, id

State == [num : 0..2, den : 0..2]

VARIABLES p

vars == <<p>>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Init == p = One

Next == p' = Half \/ p' = Norm(p)

Spec == Init /\ [][Next]_p

RationalBounds == p.num >= 0 /\ p.den >= 1

DenominatorPowerOfTwo == \E k \in {0, 1, 2} : p.den = 2 ^ k

====