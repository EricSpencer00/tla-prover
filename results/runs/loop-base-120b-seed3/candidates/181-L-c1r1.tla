---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial condition: n ranges over the finite naturals *)
Init == n \in NatOverride

(* Nondeterministic step: n may take any value in the finite range *)
Next == n' \in NatOverride

(* Overall specification *)
Spec == Init /\ [][Next]_<<n>>

(* Invariant stating that the double of any natural in the range is even *)
Inv == \A m \in NatOverride : (2 * m) % 2 = 0

(* Property to be checked by TLC *)
Properties == []Inv
====