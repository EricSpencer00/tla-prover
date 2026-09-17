---- MODULE mathd_numbertheory_64 ----
EXTENDS Naturals, TLAPS

THEOREM mathd_numbertheory_64 ==
    39 \in {x \in Nat : (30 * x) % 47 = 42} /\
    \A x \in Nat : (30 * x) % 47 = 42 => (x >= 39)BY SMT
====
