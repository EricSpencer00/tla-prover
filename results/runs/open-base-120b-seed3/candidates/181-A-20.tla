---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

(* Override of the infinite set of naturals with a finite range *)
NatOverride == 0..MaxNat

VARIABLE n

(* Initial condition: n is any natural number within the finite range *)
INIT == n \in NatOverride

(* Next-state relation: n can advance to the next natural number within the range *)
NEXT == /\ n' \in NatOverride
        /\ n' = n + 1

(* Overall specification *)
SPECIFICATION == INIT /\ [][NEXT]_n

(* Invariant stating that the double of every natural number in the range is even *)
INVARIANTS == \A m \in NatOverride : (2 * m) % 2 = 0

(* Property to be checked; same as the invariant *)
PROPERTIES == INVARIANTS
====================================================