---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS ArithmeticModules, ArithmeticOps, EqualityOps, ExtendsModules

VARIABLES p

TypeOK == p \in [num : Int, den : Int]

\* The dyadic rational equal to one.
One == [num |-> 1, den |-> 1]

\* Halve the fraction by doubling the denominator.
Half == [num |-> p.num, den |-> p.den * 2]

\* Recursive reduction: divide numerator and denominator by two while both are even.
Norm(q) == IF q.num % 2 = 0 /\ q.den % 2 = 0 THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2]) ELSE q

Init == p = One

Next == p' = Norm(p)

Spec == Init /\ [][Next]_p

DenPositive == p.den >= 1

OnlyDenominatorPowersOfTwo == (\E k \in Nat : p.den = 2 ^ k)

====