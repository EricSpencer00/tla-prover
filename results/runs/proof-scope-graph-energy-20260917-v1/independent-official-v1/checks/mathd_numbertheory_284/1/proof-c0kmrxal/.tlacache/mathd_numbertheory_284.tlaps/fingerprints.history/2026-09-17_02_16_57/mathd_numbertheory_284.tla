---- MODULE mathd_numbertheory_284 ----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_284 ==
    \A a, b \in Nat :
        (a >= 1) /\
        (a <= 9) /\
        (b <= 9) /\
        (10 * a + b = 2 * (a + b)) =>
        (10 * a + b = 18)BY SetExtensionality
====
