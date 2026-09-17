---- MODULE mathd_numbertheory_234 ----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_234 ==
    \A a, b \in Nat :
        (a >= 1) /\ (a <= 9) /\ (b <= 9) /\
        ((10 * a + b) * (10 * a + b) * (10 * a + b) = 912673)
        => (a + b = 16)
BY SMT, SetExtensionality
====
