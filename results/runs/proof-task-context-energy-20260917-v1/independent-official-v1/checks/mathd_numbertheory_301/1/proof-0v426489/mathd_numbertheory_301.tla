----- MODULE mathd_numbertheory_301 -----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_301 ==
    \A j \in Nat : (j > 0) => (3 * (7 * j + 3)) % 7 = 2BY SMT
============================================================
