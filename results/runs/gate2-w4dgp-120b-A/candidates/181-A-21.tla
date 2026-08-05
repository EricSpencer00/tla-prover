---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

VARIABLES n

NatOverride == 0 .. MaxNat

vars == <<n>>

Init == n = 0

Next == n' = IF n < MaxNat THEN n + 1 ELSE 0

Spec == Init /\ [][Next]_vars

TypeOK == n \in NatOverride

AssumeEven == (2 * n) % 2 = 0

====