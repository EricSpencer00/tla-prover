---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps ExtendsModules, FunctionApplication, IfThenElse, OperatorDefNames, RecordAccess, RecordConstructor, Specification, id

\* A dyadic rational is stored as a record with a numerator and a denominator
\* (always a power of two). The normalization operator divides both by two
\* whenever both are even, folding out the factor of two from the fraction.
Dyadic == [num : Int, den : Int]

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
              THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
              ELSE p

VARIABLES value

vars == <<value>>

Init == value = One

Halve == value' = Norm(Half(value))

Next == Halve

Spec == Init /\ [][Next]_vars

DenIsPowerOfTwo == \E k \in Nat : value.den = 2 ^ k

NoCommonFactorOfTwo == (value.num % 2 = 0 /\ value.den % 2 = 0) => (value.num = 0 /\ value.den = 0)

====