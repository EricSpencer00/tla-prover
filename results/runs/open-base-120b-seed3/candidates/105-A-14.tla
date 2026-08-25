---- MODULE DyadicRationals ----
EXTENDS Integers

\* --------------------------------------------------------------
\*  Types
\* --------------------------------------------------------------

Dyadic == { p \in [num : Int, den : Nat] :
               p.den > 0 /\ IsPowerOfTwo(p.den) }

IsPowerOfTwo(d) == \E n \in Nat : d = 2 ^ n

\* --------------------------------------------------------------
\*  Constants and Operators
\* --------------------------------------------------------------

One == [num |-> 1, den |-> 1]

Half(p) == Norm([num |-> p.num, den |-> p.den * 2])

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* --------------------------------------------------------------
\*  Variables
\* --------------------------------------------------------------

VARIABLE p

\* --------------------------------------------------------------
\*  Specification
\* --------------------------------------------------------------

Init == p = One

Next ==
    \/ p' = Half(p)
    \/ p' = p

SPECIFICATION == Init /\ [][Next]_<<p>>

INVARIANTS == /\ p \in Dyadic

PROPERTIES == TRUE

====