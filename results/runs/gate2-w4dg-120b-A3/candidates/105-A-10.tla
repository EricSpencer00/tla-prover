---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

VARIABLES p

vars == <<p>>

Init ==
    /\ p = One

Next ==
    /\ p' = Half(p)
    /\ UNCHANGED << >>

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(Next)

TypeOK ==
    /\ p \in [num : Nat, den : Nat]
    /\ p.den # 0

IntegersSpec ==
    /\ Norm(One) = Half(One)
    /\ Norm(Half(One)) = Half(Half(One))

====