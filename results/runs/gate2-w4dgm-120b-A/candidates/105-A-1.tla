---- MODULE DyadicRationals ----
EXTENDS Integers

CONSTANTS One, Half, Norm

Spec == 1

Init == Spec

Next == Spec

StateConstraint == Spec

ResultTypeOK == Spec

TypeOK == Spec

vars == {}

Spec == Init /\ [][Next]_vars
====