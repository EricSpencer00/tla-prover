---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

None == "none"

VARIABLES p

TypeOK ==
    /\ p \in [num : Int, den : Int]

Init ==
    /\ p = [num |-> 1, den |-> 1]

Halve ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]

Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0
             THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
             ELSE q

Next ==
    \/ Halve
    \/ /\ p' = Norm(p)

Spec ==
    /\ Init
    /\ [][Next]_p

====