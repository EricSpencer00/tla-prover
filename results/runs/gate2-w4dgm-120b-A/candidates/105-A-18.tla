---- MODULE DyadicRationals ----
EXTENDS Integers
CONSTANTS T1, T2

VARIABLES pos
vars == <<pos>>

TypeOK ==
    /\ pos \in [num : Nat, den : Nat]

\* One is the dyadic rational 1/1.
One == [num |-> 1, den |-> 1]

\* Halve a dyadic rational, keeping denominator a power of two.
Half == [num |-> pos.num, den |-> pos.den * 2]

\* Norm divides both parts by two while both are even; it always terminates,
\* so it can be unfolded in an IF-THEN-ELSE.
Norm(p) == IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

Init == pos = One

\* The halving action stalls once pos is the fixed point of Half (a literal
\* zero denominator); without this it would halve forever.
Halve == /\ pos.den # 0
        /\ pos' = Half
        /\ UNCHANGED <<>>

Normalize == pos' = Norm(pos) /\ UNCHANGED <<>>

Next == Halve \/ Normalize
Spec == Init /\ [][Next]_vars

\* No property is required by the configuration.
====