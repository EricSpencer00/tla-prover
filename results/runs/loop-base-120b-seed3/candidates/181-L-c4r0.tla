---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* NatOverride replaces the infinite Nat with a finite range for model checking *)
NatOverride == 0 .. MaxNat

VARIABLE n

(* Definition of evenness *)
Even(x) == x % 2 = 0

(* Initial state: n is any natural number within the finite range *)
Init == n \in NatOverride

(* Next-state relation: n may take any value in the finite range *)
Next == /\ n' \in NatOverride

(* Overall specification for TLC *)
SPECIFICATION == Init /\ [][Next]_<<n>>

(* Required identifiers with exact names *)
INIT == Init
NEXT == Next

(* Invariant stating that double of n is even *)
Invariant == Even(2 * n)

INVARIANTS == Invariant
PROPERTIES == Invariant
====