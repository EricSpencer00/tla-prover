---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication,
          IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

TypeOK == One \in [num : {1}, den : {1}] /\ Half \in [num : {1}, den : {2}]

InitState == One = [num |-> 1, den |-> 1]

SpecState == \A p \in {One, Half} : p = [num |-> p.num, den |-> p.den]

====