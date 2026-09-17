----- MODULE amc12b_2002_p11 -----
EXTENDS TLAPS, Integers

IsPrime(n) == (n > 1) /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

THEOREM amc12b_2002_p11 ==
  \A a, b \in Nat :
    (IsPrime(a) /\ IsPrime(b) /\ IsPrime(a - b) /\ IsPrime(a + b)) => (IsPrime(a + b + (a - b + (a + b))))BY SMT
=======================
