---- MODULE MC_sums_even ----
EXTENDS Naturals, Integers

CONSTANT MaxNat

(* Finite version of Nat for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Initial condition: n ranges over the finite naturals *)
INIT == n \in NatOverride

(* Nondeterministic step: n may take any value in the finite range *)
NEXT == /\ n' \in NatOverride

(* Overall specification *)
SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* Invariant stating that the double of any natural in the range is even *)
INVARIANTS == \A m \in NatOverride : (2 * m) % 2 = 0

(* Property to be checked by TLC *)
PROPERTIES == []INVARIANTS
====