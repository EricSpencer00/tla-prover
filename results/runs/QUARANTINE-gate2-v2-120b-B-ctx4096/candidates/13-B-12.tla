---- MODULE MCBakery --------------------------------
EXTENDS Bakery

(* This constant represents the maximum value for the overridden Nat set.
   It must be a natural number. *)
CONSTANT MaxNat

(* Ensure that MaxNat is a natural number. *)
ASSUME MaxNat \in Nat

(* Define NatOverride as the interval from 0 to MaxNat, inclusive.
   This overrides the default Nat set used in the Bakery module. *)
NatOverride == 0 .. MaxNat

=============================================================================