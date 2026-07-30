---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

AssumeNatBound == Nat \subseteq (0 .. MaxNat)

VARIABLES x

vars == <<x>>

TypeOK == x \in Nat

Init == \E y \in Nat : x = y

Step == \E y \in Nat : x' = y

Next == Step

Spec == Init /\ [][Next]_vars

NatNonEmpty == Nat \neq {}

====