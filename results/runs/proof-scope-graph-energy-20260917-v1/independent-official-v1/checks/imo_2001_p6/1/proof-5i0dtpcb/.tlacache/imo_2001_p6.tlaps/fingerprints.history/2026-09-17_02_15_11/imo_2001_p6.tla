---- MODULE imo_2001_p6 ----
EXTENDS TLAPS, Integers

IsPrime(n) ==    (n > 1)
              /\ \A m \in 2..(n-1) : ~ \E p \in 2..(n-1) : n = m * p

THEOREM imo_2001_p6 ==
  \A a, b, c, d \in Nat :
    (a > 0 /\ b > 0 /\ c > 0 /\ d > 0) /\
    (a > b) /\ (b > c) /\ (c > d) /\
    (a * c + b * d = (b + d + a - c) * (b + d + c - a))
    =>
    ~IsPrime(a * b + c * d)BY SMT DEF IsPrime
====
