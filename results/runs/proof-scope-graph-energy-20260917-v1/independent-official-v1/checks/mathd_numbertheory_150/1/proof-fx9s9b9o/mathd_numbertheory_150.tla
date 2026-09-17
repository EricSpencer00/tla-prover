---- MODULE mathd_numbertheory_150 ----
EXTENDS TLAPS, Integers

Divides(d, p) == \E q \in Nat : p = q * d

IsPrime(p) ==
  p > 1 /\
  \A d \in 2..(p-1) : ~ \E q \in Nat : p = q * d

THEOREM mathd_numbertheory_150 ==
  \A n \in Nat : ~IsPrime(7 + 30 * n) => n >= 6
BY SMT DEF Divides, IsPrime
====
