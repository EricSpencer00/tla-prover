---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm
VARIABLES p

TypeOK ==
    /\ p \in [num : Nat, den : Nat]

Init ==
    /\ p = One

Halve ==
    /\ p' = [num |-> p.num, den |-> p.den * 2]

NormStep ==
    /\ p.num % 2 = 0 /\ p.den % 2 = 0
    /\ p' = Norm([num |-> p.num \div 2, den |-> p.den \div 2])

Next ==
    \/ Halve
    \/ NormStep

Specification == Init /\ [][Next]_p

DenominatorPowerOfTwo ==
    \E k \in Nat : p.den = 2 ^ k

FractionInRange ==
    /\ p.num >= 0
    /\ p.num <= p.den

====