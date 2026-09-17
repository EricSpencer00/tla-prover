---- MODULE mathd_numbertheory_370 ----
EXTENDS TLAPS, Integers


THEOREM mathd_numbertheory_370 ==
    \A n \in Nat : (n % 7 = 3) => ((2 * n + 1) % 7 = 0)BY SMT
====
