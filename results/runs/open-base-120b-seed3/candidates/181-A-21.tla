---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial predicate *)
INIT == n \in NatOverride

(* Next-state relation *)
NEXT == n' \in NatOverride

(* Specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Invariant asserting that double of any natural number is even *)
EvenDouble == (2 * n) % 2 = 0

INVARIANTS == EvenDouble

(* Property to be checked (same as the invariant) *)
PROPERTIES == EvenDouble

====