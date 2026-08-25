---- MODULE MCBoulanger ----
EXTENDS Naturals, Boulanger

CONSTANTS N, MaxNat

(* Finite version of the natural numbers, used to override Nat in the
   Boulanger specification during model checking. *)
NatOverride == 0 .. MaxNat

====