---- MODULE mathd_numbertheory_99 ----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_99 ==
    \A n \in Nat : (2 * n) % 47 = 15 => (n % 47 = 31)BY SMT
====
