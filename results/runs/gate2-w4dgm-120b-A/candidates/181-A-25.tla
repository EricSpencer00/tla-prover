---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

ASSUME MaxNat \in Nat /\ MaxNat = 1000000

NatOverride == (0 .. MaxNat)

VARIABLES num

vars == <<num>>

TypeOK == num \in NatOverride

Init == num = 0

Increment == num < MaxNat /\ num' = num + 1

Drop == num = MaxNat /\ num' = 0

Next == Increment \/ Drop

Spec == Init /\ [][Next]_vars

\* The theorem is assumed here so TLC can run; it is not proved in this module.
TheoremAssumed == \A n \in Nat : 2 * n = (n + n)

====