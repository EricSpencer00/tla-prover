---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANTS MaxNat, Nat

VARIABLES x, y
vars == <<x, y>>

Init ==
    /\ x \in Nat /\ y \in Nat
    /\ x = 0 /\ y = 0

Next ==
    \/ \E n \in Nat :
        /\ x' = n
        /\ UNCHANGED y
    \/ \E n \in Nat :
        /\ y' = n
        /\ UNCHANGED x

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ x \in Nat
    /\ y \in Nat

TheoremHolds ==
    (2 * x) % 2 = 0

====