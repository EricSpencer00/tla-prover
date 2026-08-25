---- MODULE DyadicRationals ----
EXTENDS Integers

\* ----------------------------------------------------------------------
\* Record type for dyadic rationals (numerator may be any integer,
\* denominator a positive power of two)
\* ----------------------------------------------------------------------
IsPowerOfTwo(n) == 
    /\ n \in Nat
    /\ \E k \in Nat : n = 2^k

Dyadic == { p \in [num : Int, den : Nat] :
               p.den > 0 /\ IsPowerOfTwo(p.den) }

\* ----------------------------------------------------------------------
\* Constants and operators
\* ----------------------------------------------------------------------
One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

RECURSIVE Norm(_)
Norm(p) == 
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\* Variables and state predicates
\* ----------------------------------------------------------------------
VARIABLES p

Init == p = One

Next == 
    \/ p' = Half(p)
    \/ p' = Norm(p)

\* ----------------------------------------------------------------------
\* Specification components required by the task
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<p>>

INVARIANTS == p \in Dyadic

PROPERTIES == TRUE

====