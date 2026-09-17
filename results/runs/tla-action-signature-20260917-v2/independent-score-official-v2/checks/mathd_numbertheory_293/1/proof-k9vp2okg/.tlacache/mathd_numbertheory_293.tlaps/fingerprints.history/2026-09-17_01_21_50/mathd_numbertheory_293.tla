---- MODULE mathd_numbertheory_293 ----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_293 ==
    \A n \in Nat :
        (n <= 9) /\ ((2007 + 10 * n) % 11 = 0) => (n = 5)
BY SMT
====
