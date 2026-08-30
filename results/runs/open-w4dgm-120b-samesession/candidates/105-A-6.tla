---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, IfThenElse, FunctionApplication, OperatorDefNames, RecordConstructor, RecordAccess

VARIABLES p

vars == << p >>

One == [num |-> 1, den |-> 1]

Half == [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN
        Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Init == p = One

Spec == Init

SpecInv == Spec

SpecProp == Spec
====