---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm, p

VARIABLES val

TypeOK ==
    /\ One \in [num : 1..1, den : 1..1]
    /\ Half \in [num : 2..2, den : 1..1]
    /\ Norm \in [num : 0..2, den : 1..2]
    /\ val \in [num : 0..2, den : 1..2]

Init ==
    /\ One = [num |-> 1, den |-> 1]
    /\ Half = [num |-> 2, den |-> 1]
    /\ Norm = [num |-> 0, den |-> 0]
    /\ val = One

Next ==
    /\ p \in {[num |-> 1, den |-> 1], [num |-> 2, den |-> 1]}
    /\ IF p.num % 2 = 0 /\ p.den % 2 = 0
       THEN Norm = [num |-> p.num \div 2, den |-> p.den \div 2]
       ELSE Norm = p
    /\ val' = Norm
    /\ UNCHANGED <<One, Half>>

Specification ==
    /\ Init
    /\ Next

InitInv == Init

NextInv == Next

SpecInv == Specification

Behave == Specification

====