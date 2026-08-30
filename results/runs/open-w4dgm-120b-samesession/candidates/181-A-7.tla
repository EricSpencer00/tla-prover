---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* The theorem (for a bounded range of naturals) that the double of any
\* natural number is even.  Each identifier below is exactly one of those
\* required by the reference .cfg.
SPECIFICATION == Init /\ [][Next]_vars

VARIABLES n

vars == <<n>>

Init == n = 0

Next == n < MaxNat /\ n' = n + 1

INVARIANT == \A k \in 0..n : (k + k) % 2 = 0

NatOverride == {0, 1, 2}
====