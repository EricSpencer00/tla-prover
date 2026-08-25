---- MODULE MC_sums_even ----
EXTENDS Naturals

CONSTANT MaxNat

VARIABLE n

(* Finite version of the natural numbers, used for model checking *)
NatOverride == 0 .. MaxNat

(* ----------------------------------------------------------------------
   State predicate and action definitions
   ---------------------------------------------------------------------- *)

INIT == n \in NatOverride

NEXT == /\ n' \in NatOverride

SPECIFICATION == INIT /\ [][NEXT]_<<n>>

(* ----------------------------------------------------------------------
   Invariant stating that the double of any natural number is even
   ---------------------------------------------------------------------- *)

EvenDouble == \A m \in NatOverride : (2 * m) % 2 = 0

INVARIANTS == { EvenDouble }

PROPERTIES == { EvenDouble }

====