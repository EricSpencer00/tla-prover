---- MODULE exercise_5_13 ----
EXTENDS Integers, TLAPS

IsPrime(n) ==    (n > 1)
              /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

Divides(a, b) == \E k \in Int : b = a * k

THEOREM exercise_5_13 ==
  \A p, x \in Int :
    IsPrime(p) /\ Divides(p, x*x*x*x - x*x + 1)
    => (p % 12 = 1)BY DEF IsPrime, Divides
====
