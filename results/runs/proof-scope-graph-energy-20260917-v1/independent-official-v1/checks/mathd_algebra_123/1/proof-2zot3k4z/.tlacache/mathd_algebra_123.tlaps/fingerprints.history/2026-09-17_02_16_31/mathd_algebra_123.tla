------------------------------- MODULE mathd_algebra_123 -------------------------------
EXTENDS Naturals, TLAPS

THEOREM mathd_algebra_123 ==
    \A a, b \in Nat :
        (a > 0) /\ (b > 0) /\ (a + b = 20) /\ (a = 3 * b) => (a - b = 10)BY SetExtensionality
=============================================================================
