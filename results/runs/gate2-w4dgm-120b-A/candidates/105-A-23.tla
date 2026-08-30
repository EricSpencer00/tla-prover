---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps,
          ExtendsModules, FunctionApplication, IfThenElse,
          OperatorDefNames, RecordAccess, RecordConstructor,
          Specification, id

VARIABLES p

vars == <<p>>

Init == p = [num |-> 1, den |-> 1]

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
           THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
           ELSE p

Next == \E q \in {One, Half, Norm(p)} : p' = q

Spec == Init /\ [][Next]_vars

NoLossDenom == p.den >= 1

ResultUnique == \A p1, p2 \in {One, Half, Norm(p)} : p1 = p2

====