---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLE p

\* The dyadic rational representing one
One == [num |-> 1, den |-> 1]

\* Halving operator: keep numerator, double the denominator
Half(q) == [num |-> q.num, den |-> q.den * 2]

\* Recursive normalization: divide numerator and denominator by 2 while both are even
RECURSIVE Norm(_)
Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

\* Initial state (the rational one)
INIT == p = One

\* Possible state transition: either halve or normalize
NEXT ==
    \/ p' = Half(p)
    \/ p' = Norm(p)

\* Full specification
SPECIFICATION == INIT /\ [][NEXT]_<<p>>

\* Invariant: denominator is always a power of two
INVARIANTS ==
    \A r \in {p} : \E k \in Nat : r.den = 2^k

\* Additional properties (trivial placeholder)
PROPERTIES == TRUE

====