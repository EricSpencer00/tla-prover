---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n ranges over the finite NatOverride *)
Init == n \in NatOverride

(* Next-state relation: n can take any value in NatOverride *)
Next == n' \in NatOverride

vars == <<n>>

(* Full specification of the system *)
Spec == Init /\ [][Next]_vars

(* Predicate stating that a number is even *)
IsEven(m) == \E k \in NatOverride : m = 2 * k

(* Invariant: double of any reachable n is even *)
Invariant == IsEven(2 * n)

INVARIANTS == Invariant

PROPERTIES == INVARIANTS
====