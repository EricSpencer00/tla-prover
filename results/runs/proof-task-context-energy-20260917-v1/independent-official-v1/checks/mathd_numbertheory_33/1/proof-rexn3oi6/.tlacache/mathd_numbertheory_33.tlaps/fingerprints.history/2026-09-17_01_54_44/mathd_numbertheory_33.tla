----- MODULE mathd_numbertheory_33 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_33 ==
  \A n \in Nat :
    (n < 398) /\ ((n * 7) % 398 = 1) => (n = 57)BY SMT
====
