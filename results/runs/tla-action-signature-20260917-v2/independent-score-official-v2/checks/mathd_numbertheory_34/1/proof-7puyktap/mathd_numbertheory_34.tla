----- MODULE mathd_numbertheory_34 -----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_34 ==
    \A x \in Nat :
        (x < 100) /\ ((x * 9) % 100 = 1) => (x = 89)BY SMT
====
