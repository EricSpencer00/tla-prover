---- MODULE mathd_numbertheory_320 ----
EXTENDS TLAPS, Integers

Divides(a, b) == \E k \in Nat : b = a * k

THEOREM mathd_numbertheory_320 ==
    \A n \in Nat :
        (n < 101) /\ Divides(101, 123456 - n) => (n = 34)BY SMT DEF Divides
=====================================================
