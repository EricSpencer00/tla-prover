---- MODULE DyadicRationals ----
EXTENDS Integers

VARIABLES p

TypeOK ==
    /\ p \in [num : 0..4, den : 0..8]

Init ==
    /\ p = [num |-> 1, den |-> 1]

One ==
    [num |-> 1, den |-> 1]

Half ==
    [num |-> p.num, den |-> p.den * 2]

Norm(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN Norm([num |-> q.num \div 2, den |-> q.den \div 2])
    ELSE q

Next ==
    \/ p' = Half
    \/ p' = Norm(p)

NextP == Next

Spec ==
    /\ Init
    /\ [][NextP]_p
    /\ \A p2 \in [num : 0..4, den : 0..8] : TRUE

DenominatorPowerOfTwo ==
    \E k \in Nat : p.den = 2 ^ k

RationalConsistent ==
    \A p2 \in [num : 0..4, den : 0..8] : (p2 = Norm(p2)) => p2 = One

====