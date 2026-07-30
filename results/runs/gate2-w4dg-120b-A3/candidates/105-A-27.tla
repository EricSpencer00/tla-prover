---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS p

VARIABLES rat

vars == <<rat>>

TypeOK ==
    /\ rat \in [num : 0..3, den : 1..4]

Init ==
    /\ rat = [num |-> 1, den |-> 1]

Halve(r) ==
    IF r.den = 4
    THEN [num |-> r.num, den |-> 2]
    ELSE [num |-> r.num, den |-> r.den * 2]

Norm(p) ==
    IF p.num % 2 = 0 /\ p.den % 2 = 0
    THEN Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    ELSE p

Next ==
    \/ \E r \in {Norm(rat), One, Half} : rat' = Halve(r)
    \/ \E r \in {Norm(rat), One, Half} : rat' = Norm(r)

Spec == Init /\ [][Next]_vars

One == [num |-> 1, den |-> 1]

Half == Norm([num |-> 1, den |-> 2])

Inv == TRUE

Prop == TRUE

====