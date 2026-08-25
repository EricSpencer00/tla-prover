---- MODULE DyadicRationals ----
EXTENDS Integers

\* -------------------------------------------------
\* Dyadic rationals are represented as records with
\*   num : integer   (numerator)
\*   den : natural   (denominator, a positive power of two)
\* -------------------------------------------------

IsPowerOfTwo(d) == 
    /\ d > 0
    /\ \E n \in Nat : 2^n = d

Dyadic == { p \in [num : Int, den : Nat] : IsPowerOfTwo(p.den) }

\* -----------------------------------------------------------------
\* Operator definitions required by the description
\* -----------------------------------------------------------------

One == [num |-> 1, den |-> 1]

Half(p) == [num |-> p.num, den |-> p.den * 2]

Norm(p) == 
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

\* -----------------------------------------------------------------
\* Stub definitions for the usual TLC identifiers
\* -----------------------------------------------------------------

SPECIFICATION == TRUE

INIT == TRUE

NEXT == UNCHANGED <<>>

INVARIANTS == {}

PROPERTIES == {}

=============================================================================