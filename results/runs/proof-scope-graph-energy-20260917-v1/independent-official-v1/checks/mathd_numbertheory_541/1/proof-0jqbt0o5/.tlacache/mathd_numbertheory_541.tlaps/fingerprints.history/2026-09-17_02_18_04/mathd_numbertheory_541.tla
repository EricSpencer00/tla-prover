---- MODULE mathd_numbertheory_541 ----
EXTENDS TLAPS, Integers

THEOREM mathd_numbertheory_541 ==
    \A m, n \in Nat :
        (m > 1 /\ n > 1 /\ m * n = 2005) => m + n = 406
BY SetExtensionality
====
