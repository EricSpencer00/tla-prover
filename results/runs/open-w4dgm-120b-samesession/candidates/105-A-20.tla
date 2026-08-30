---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

One == [num |-> 1, den |-> 1]

Half == [num |-> 1, den |-> 2]

RECURSIVE Norm(_)
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2]) ELSE p

VARIABLES value

vars == <<value>>

Init == value = One

Halve == value' = Half

Normalize == value' = Norm(value)

Next == Halve \/ Normalize

Spec == Init /\ [][Next]_vars

DenominatorIsPowerOfTwo == \E k \in Nat : value.den = 2 ^ k

EveryFractionIsDyadic == value.num \in Nat /\ value.den \in Nat

====