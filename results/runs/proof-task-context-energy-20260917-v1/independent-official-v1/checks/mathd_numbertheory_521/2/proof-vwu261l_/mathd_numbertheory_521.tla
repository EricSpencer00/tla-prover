----- MODULE mathd_numbertheory_521 -----
EXTENDS Naturals, TLAPS

Even(x) == x % 2 = 0

THEOREM mathd_numbertheory_521 ==
    \A m, n \in Nat :
        (Even(m) /\ Even(n) /\ m - n = 2 /\ m * n = 288)
        => m = 18BY DEF Even
=============================================================================
