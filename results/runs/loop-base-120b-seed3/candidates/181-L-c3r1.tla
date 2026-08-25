---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

Init == n \in NatOverride

Next == n' \in NatOverride

Spec == Init /\ [][Next]_<<n>>

INVARIANTS == \A m \in NatOverride : (2 * m) % 2 = 0

PROPERTIES == INVARIANTS
====