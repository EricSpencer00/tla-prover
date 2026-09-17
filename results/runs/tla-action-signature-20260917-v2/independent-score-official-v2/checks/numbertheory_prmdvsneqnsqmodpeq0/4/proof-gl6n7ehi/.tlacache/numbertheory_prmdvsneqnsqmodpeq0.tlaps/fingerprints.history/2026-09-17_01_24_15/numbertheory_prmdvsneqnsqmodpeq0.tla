---- MODULE numbertheory_prmdvsneqnsqmodpeq0 ----
EXTENDS Naturals, TLAPS

Divides(a, b) == \E k \in Nat : b = a * k

IsPrime(n) ==    (n > 1)
              /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

THEOREM numbertheory_prmdvsneqnsqmodpeq0 ==
  \A n, p \in Nat :
    IsPrime(p) =>
    (Divides(p, n) <=> ((n*n) % p = 0))BY SMT, SetExtensionality
====
