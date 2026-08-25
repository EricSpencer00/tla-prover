---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial state: n is any natural number within the finite range *)
Init == n \in NatOverride

(* Next-state relation: n can evolve to any value in the finite range *)
Next == n' \in NatOverride

(* Temporal specification *)
Spec == Init /\ [][Next]_<<n>>

(* Invariant stating that double of any natural number is even *)
Inv == \A m \in NatOverride : (2 * m) % 2 = 0

PROPERTIES == Inv
====