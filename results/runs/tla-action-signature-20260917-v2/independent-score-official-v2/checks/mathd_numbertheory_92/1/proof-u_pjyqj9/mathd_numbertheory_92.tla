----- MODULE mathd_numbertheory_92 -----
EXTENDS TLAPS, Integers


THEOREM mathd_numbertheory_92 ==
    \A n \in Nat : (5 * n) % 17 = 8 => (n % 17 = 5)BY SMT
====
