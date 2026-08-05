---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

RECURSIVE Norm(_)
Norm(p) ==
    LET recursiveStep == Norm([num |-> p.num \div 2, den |-> p.den \div 2])
    IN IF p.num % 2 = 0 /\ p.den % 2 = 0 THEN recursiveStep ELSE p

VARIABLES pos
vars == <<pos>>

TypeOK ==
    /\ pos \in {One, Half, Norm(One), Norm(Half)}

Init ==
    /\ pos = One

Step ==
    /\ \/ pos' = Half
       \/ pos' = Half
       \/ pos' = Norm(pos)
    /\ UNCHANGED vars

Spec ==
    /\ Init
    /\ [][Step]_vars

====