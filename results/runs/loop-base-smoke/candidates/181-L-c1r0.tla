---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n is any natural number in the finite range *)
INIT == n \in NatOverride

(* Next-state relation: nondeterministically choose any value in the finite range *)
NEXT == n' \in NatOverride

(* Overall specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Invariant stating that double of the current n is even *)
INVARIANTS == (2 * n) % 2 = 0

(* Property (theorem) that for all numbers in the finite range, double is even *)
PROPERTIES == \A m \in NatOverride : (2 * m) % 2 = 0
====