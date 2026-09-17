----- MODULE induction_divisibility_3divnto3m2n -----
EXTENDS TLAPS, Integers

Divides(a, b) == \E k \in Nat : b = k * a

THEOREM induction_divisibility_3divnto3m2n ==
  \A n \in Nat : Divides(3, (n*n*n + 2*n))BY SMT, NoSetContainsEverything
====
