----- MODULE amc12_2000_p6 -----
EXTENDS TLAPS, Naturals

IsPrime(n) == (n > 1) /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

THEOREM amc12_2000_p6 ==
    \A p, q \in Nat : (IsPrime(p) /\ IsPrime(q) /\ p # q) => (p * q - (p + q) # 194)BY DEF IsPrime
====
