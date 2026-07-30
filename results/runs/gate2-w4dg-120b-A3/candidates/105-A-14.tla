---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a fraction p.num / p.den where the denominator is
\* a power of two, so doubling the denominator keeps us in the dyadic set.
\* Normalization keeps numerators and denominators odd by cancelling powers
\* of two from both at once, repeatedly.

\* The following identifiers are required by the .cfg and must appear exactly
\* as they read: One, Half, Norm, id, Specification, Init, Next,
\* Invariants, and Properties.

One == [num |-> 1, den |-> 1]

\* Halve the dyadic rational, leaving the denominator a power of two.
Half(r) == [num |-> r.num, den |-> r.den * 2]

\* Repeatedly cancel a common factor of two from numerator and denominator.
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

id == 105

Specification == One

VARIABLES r
vars == <<r>>

TypeOK == r \in [num : INTEGER, den : INTEGER]

Init == r = One

Next == r' = Half(r) \/ r' = Norm(r)

Spec == Init /\ [][Next]_vars

Invariants == TypeOK

Properties == Spec
====