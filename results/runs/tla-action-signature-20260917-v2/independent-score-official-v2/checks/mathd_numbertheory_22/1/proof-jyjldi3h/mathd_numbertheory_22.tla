----- MODULE mathd_numbertheory_22 -----

EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_22 ==
    \A b \in Nat :
        b < 10 /\
        (\E n \in Nat : n * n = 10 * b + 6) =>
        (b = 1) \/ (b = 3)BY SMT
====
