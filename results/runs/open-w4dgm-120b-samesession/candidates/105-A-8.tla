---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

DyadicValues == [num : Int, den : Int]

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

VARIABLES held, lastNorm, steps

vars == <<held, lastNorm, steps>>

Init ==
    /\ held = One
    /\ lastNorm = One
    /\ steps = 0

Halve ==
    /\ held' = [num |-> held.num, den |-> held.den * 2]
    /\ UNCHANGED <<lastNorm, steps>>

Normalize ==
    /\ held' = Norm(held)
    /\ lastNorm' = Norm(held)
    /\ steps' = steps + 1

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

NormalizationEventuallyStabilizes == (held # lastNorm) ~> (held = lastNorm)

====