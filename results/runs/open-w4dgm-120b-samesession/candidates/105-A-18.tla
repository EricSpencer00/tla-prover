---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

Operators == [num : Int, den : Int]

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

Spec == Specification

VARIABLES rat

vars == <<rat>>

Init == rat = One

Next == rat' = Half

TypeOK == rat \in Operators

StateConstraint == rat.den \in {1, 2, 4, 8, 16}

SpecOK == Spec = Specification

SpecStateConstraint == rat.den <= 16

NextState ==
    /\ Next
    /\ TypeOK
    /\ StateConstraint
    /\ SpecOK
    /\ SpecStateConstraint

Spec == Init /\ [][Next]_vars

====