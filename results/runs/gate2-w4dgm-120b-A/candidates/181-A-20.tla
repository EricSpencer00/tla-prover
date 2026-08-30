---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANTS MaxNat

NatOverride == 0 .. MaxNat

ASSUME MaxNat \in Nat

VARIABLES n

vars == << n >>

Init0 == n = 0

Nxt0 == n < MaxNat /\ n' = n + 1

Init == Init0
Next == Nxt0
Spec == Init \/ [][Next]_vars

TypeOK == n \in NatOverride

NoMisstep == 2 * n \in NatOverride

====