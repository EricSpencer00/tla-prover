----- MODULE mathd_numbertheory_1124 -----
EXTENDS TLAPS, Integers

Divides(a, b) == \E k \in Nat : b = a * k

THEOREM mathd_numbertheory_1124 ==
  \A n \in Nat :
    n <= 9 /\ Divides(18, 3740 + n)
    => (n = 4)BY SMT DEF Divides
====
