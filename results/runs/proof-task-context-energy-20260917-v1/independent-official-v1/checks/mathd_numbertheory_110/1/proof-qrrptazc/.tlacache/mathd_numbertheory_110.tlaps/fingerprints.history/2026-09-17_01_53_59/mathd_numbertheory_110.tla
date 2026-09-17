----- MODULE mathd_numbertheory_110 -----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_110 ==
    \A a, b \in Nat :
        (a > 0) /\ (b > 0) /\ (b <= a) /\ ((a + b) % 10 = 2) /\ ((2 * a + b) % 10 = 1) => ((a - b) % 10 = 6)BY SetExtensionality
====
