---- MODULE mathd_numbertheory_247 ----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_247 ==
    \A n \in Nat : (3 * n) % 11 = 2 => (n % 11 = 8)BY SMT
====
