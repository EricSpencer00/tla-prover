---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS

VARIABLES p

\* ----------------------------------------------------------------------
\*  Operator definitions
\* ----------------------------------------------------------------------
RECURSIVE Norm(_)

One == [num |-> 1, den |-> 1]

Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* ----------------------------------------------------------------------
\*  Helper definitions
\* ----------------------------------------------------------------------
IsPowerOfTwo(d) == \E i \in Nat : d = 2 ^ i

Dyadic == { q \in [num : Int, den : Nat] :
            q.den > 0 /\ IsPowerOfTwo(q.den) }

\* ----------------------------------------------------------------------
\*  Specification components
\* ----------------------------------------------------------------------
Init == p = One

Next ==
    \/ p' = Half(p)
    \/ UNCHANGED p

INVARIANTS == p \in Dyadic

PROPERTIES == TRUE

SPECIFICATION == Init /\ [] [Next]_<<p>> /\ INVARIANTS

====