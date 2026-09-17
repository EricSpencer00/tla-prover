---- MODULE mathd_numbertheory_780 ----
EXTENDS Integers, TLAPS

THEOREM mathd_numbertheory_780 ==
    \A m, x \in Int :
        (0 <= x) /\
        (10 <= m) /\ (m <= 99) /\
        (6 * x) % m = 1 /\
        (x - 36) % m = 0
        => m = 43BY SMT, SetExtensionality
====
