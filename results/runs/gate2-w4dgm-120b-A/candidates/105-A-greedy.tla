---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

One == [num |-> 1, den |-> 1]

Half == [num |-> One.num, den |-> One.den * 2]

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES val

vars == <<val>>

Init == val = One

Halve == val' = Half

Normalize == val' = Norm(val)

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

ValueIsDyadic == val.den >= 1 /\ val.den % 2 = 0

DenominatorIsPowerOfTwo == \E k \in Nat : val.den = 2 ^ k

====