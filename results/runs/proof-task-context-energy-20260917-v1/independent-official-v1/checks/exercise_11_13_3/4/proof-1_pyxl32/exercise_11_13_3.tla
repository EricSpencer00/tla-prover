---------------------------- MODULE exercise_11_13_3 ----------------------------
EXTENDS Naturals, TLAPS

Divides(d, p) == \E k \in Nat : p = d * k

IsPrime(n) ==    (n > 1)
              /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

THEOREM exercise_11_13_3 ==
  \A N \in Nat : \E p \in Nat :
    p >= N /\ IsPrime(p) /\ (p + 1) % 4 = 0BY SMT, NoSetContainsEverything
=============================================================================
