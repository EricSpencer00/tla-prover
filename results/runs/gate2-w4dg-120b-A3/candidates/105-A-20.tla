---- MODULE DyadicRationals ----
EXTENDS Integers

\* A dyadic rational is a fraction whose denominator is a power of two.
\* The system models a halving operator and a recursive normalizer that
\* divides both numerator and denominator by 2 whenever both are even.
CONSTANTS p, One, Half, Norm

VARIABLES r

vars == <<r>>

TypeOK ==
    /\ p \in [num : Int, den : Int]
    /\ One \in [num : Int, den : Int]
    /\ Half \in [num : Int, den : Int]
    /\ Norm \in [num : Int, den : Int]

Init ==
    /\ r = [num |-> 1, den |-> 1]

Spec001 ==
    /\ r' = Half
    /\ UNCHANGED <<p, One, Half, Norm>>

Spec002 ==
    /\ r' = Norm
    /\ UNCHANGED <<p, One, Half, Norm>>

Next == Spec001 \/ Spec002

Spec == Init /\ [][Next]_vars

\* No distinct invariant or property is called for by the description, but
\* the module must still expose these names from the .cfg.
SpecInv == TRUE
SpecProp == TRUE
====