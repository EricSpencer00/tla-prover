---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Finite version of the natural numbers for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state predicate expected by TLC (named Init) *)
Init == n \in NatOverride

(* Next-state relation expected by TLC (named Next) *)
Next == n' \in NatOverride

(* Overall specification (optional, not required by TLC) *)
Spec == Init /\ [][Next]_<<n>>

(* Invariant stating that double of the current n is even *)
Inv == (2 * n) % 2 = 0

(* Property (theorem) that for all numbers in the finite range, double is even *)
Prop == \A m \in NatOverride : (2 * m) % 2 = 0
====