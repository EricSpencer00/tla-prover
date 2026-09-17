----- MODULE mathd_algebra_125 -----
EXTENDS TLAPS, Integers

THEOREM mathd_algebra_125 ==
    \A x, y \in Nat :
        (x > 0) /\ (y > 0) /\ (y = 5 * x) /\ ((x - 3) + (y - 3) = 30) => x = 6BY SetExtensionality
====
