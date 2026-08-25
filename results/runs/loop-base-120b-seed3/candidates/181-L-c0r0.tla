---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

Init == n \in NatOverride

Next == n' \in NatOverride

vars == <<n>>

SPECIFICATION == Init /\ [][Next]_vars

IsEven(m) == \E k \in NatOverride : m = 2 * k

INVARIANTS == IsEven(2 * n)

PROPERTIES == INVARIANTS
====