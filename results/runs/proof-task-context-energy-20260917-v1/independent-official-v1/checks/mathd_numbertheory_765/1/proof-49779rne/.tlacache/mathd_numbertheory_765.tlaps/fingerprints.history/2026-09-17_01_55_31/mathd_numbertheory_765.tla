----- MODULE mathd_numbertheory_765 -----

EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_765 ==
    \A x \in Int :
        (x < 0) /\ (24 * x % 1199 = 15) => (x <= -449)
BY SMT
====
