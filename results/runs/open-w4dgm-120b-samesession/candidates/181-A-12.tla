---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat

\* Finite override: this is the only definition in the module; Nat is never
\* declared here, so the .cfg replacement is what makes Nat finite.
NatOverride == 0..MaxNat

VARIABLES x

vars == <<x>>

Spec == Init /\ [][Next]_vars

Init == x = 0

Next == x' = IF x = MaxNat THEN 0 ELSE x + 1

Inv == x \in NatOverride

Theorem == \A n \in NatOverride : 2 * n \in NatOverride

====