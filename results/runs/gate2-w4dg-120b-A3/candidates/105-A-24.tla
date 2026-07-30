---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

TypeOK ==
    /\ One \in [num : 1..3, den : 1..4]
    /\ Half \in [num : 1..3, den : 1..4]
    /\ Norm \in [num : 1..3, den : 1..4]

Init ==
    /\ p = Half

\* Conditionally normalise a fraction by dividing both components by two when they
\* are both even, leaving it untouched otherwise (the conditional is the IF/THEN/ELSE).
Normalize(q) ==
    IF q.num % 2 = 0 /\ q.den % 2 = 0
    THEN [num |-> q.num \div 2, den |-> q.den \div 2]
    ELSE q

Spec ==
    /\ p' = Normalize(p)
    /\ UNCHANGED <<One, Half, Norm>>

Next == Spec

SpecInv == TRUE

SpecTypeOK == TRUE

====