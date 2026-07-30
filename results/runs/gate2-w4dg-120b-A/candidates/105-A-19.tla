---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a fraction with denominator a power of two; the
\* fraction is kept in lowest terms by the Norm function (division by 2
\* of both numerator and denominator while both are even). "One" and "Half"
\* are the two base values from which all others are built.
RECURSIVE Norm(_)
Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

One == [num |-> 1, den |-> 1]
Half == [num |-> 1, den |-> 2]

VARIABLES r
vars == <<r>>

Init == r = One
Next == r' = Norm([num |-> r.num, den |-> r.den * 2])

\* The model has no external specification -- the set of reachable states
\* from Init by repeated Next is the entire spec, so SPECIFICATION is
\* simply Init /\ [][Next]_vars, the usual safety format.
Specification == Init /\ [][Next]_vars

TypeOK == r \in [num : Nat, den : Nat]
Reachable == r \in { s \in [num : Nat, den : Nat] : s = One \/ \E k \in Nat : s = Norm([num |-> 1, den |-> 2^k]) }
====