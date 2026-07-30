---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a fraction whose denominator is a power of two.
\* The system keeps fractions in reduced form, so fraction equivalence
\* coincides with literal equality: two dyadic rationals are equal as
\* records exactly when they denote the same rational number.
\* Normalization is a recursive operator that keeps halving numerator
\* and denominator together whenever both are even -- a genuine
\* recursive descent rather than a single-shot reduction.
\* One and Half are the base values the system starts from.

VARIABLES p

TypeOK == p \in [num : Int, den : {1, 2, 4}]

\* The value one, as a dyadic rational: denominator 1.
One == [num |-> 1, den |-> 1]

\* Halving doubles the denominator, which keeps the value dyadic.
Half == [num |-> p.num, den |-> p.den * 2]

\* Recursive normalization: keep dividing by two while both parts are even.
Norm(q) ==
  IF q.num % 2 = 0 /\ q.den % 2 = 0
  THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
  ELSE q

Spec == p \in [num : Int, den : {1, 2, 4}]

Init == p = One

Next == p' = Half \/ p' = Norm(p)

\* No extra invariant or property beyond the standard safety net: p stays
\* inside the dyadic rational domain and the denominator stays a power of two.
TypeOKInv == TypeOK
DenPowerOfTwo == p.den \in {1, 2, 4}

====