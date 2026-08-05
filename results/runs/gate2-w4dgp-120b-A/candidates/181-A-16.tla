---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

VARIABLES n
vars == <<n>>

NatOverride == 0..MaxNat

NextNat(n) == IF n < MaxNat THEN n + 1 ELSE 0

Init == n = 0

Step == n' = NextNat(n)

Spec == Init /\ [][Step]_vars

NatBound == MaxNat <= 1000000

====