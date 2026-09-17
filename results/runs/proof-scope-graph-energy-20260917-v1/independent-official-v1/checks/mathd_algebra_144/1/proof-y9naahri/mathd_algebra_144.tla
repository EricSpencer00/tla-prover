----- MODULE mathd_algebra_144 -----
EXTENDS TLAPS, Integers

THEOREM mathd_algebra_144 ==
    \A a, b, c, d \in Nat :
        (a > 0) /\ (b > 0) /\ (c > 0) /\ (d > 0) /\ (c - b = d) /\ (b - a = d) /\ (a + b + c = 60) /\ (a + b > c) => d < 10BY SetExtensionality
====
