----- MODULE exercise_5_28 -----
EXTENDS TLAPS, Integers

IsPrime(n) ==    (n > 1)
              /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

THEOREM exercise_5_28 ==
    \A p \in Nat :
    (IsPrime(p) /\ p % 4 = 1) =>
    (\E x \in Nat : (x*x*x*x) % p = 2 <=> \E A, B \in Nat : p = A*A + 64*B*B)
BY SMT
=============================================================================
