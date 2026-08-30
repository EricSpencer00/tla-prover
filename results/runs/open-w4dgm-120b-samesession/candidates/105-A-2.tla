---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES fraction

vars == <<fraction>>

TypeOK == fraction \in {[num : Nat, den : Nat]}

Init == fraction = One

Halve == fraction' = Half

Next == Halve \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

StateConstraint == TypeOK

StateConstraintOK == StateConstraint

====