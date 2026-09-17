---- MODULE imo_1987_p4 ----
EXTENDS TLAPS, Integers

THEOREM imo_1987_p4 ==
    \A f \in [Nat -> Nat] :
        \E n \in Nat : f[f[n]] # n + 1987BY SMT
====
