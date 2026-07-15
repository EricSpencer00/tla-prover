---- MODULE MCBakery ----
EXTENDS Bakery

(* The constant MaxNat is intended to define the upper bound of the
   overridden natural numbers.  In the original version the assumption
   `MaxNat \notin Nat` makes the model inconsistent, because MaxNat is
   then guaranteed to be outside the set of natural numbers.  As a
   result TLC aborts with the message that the assumption is false. *)

CONSTANT MaxNat

(* MaxNat must be a natural number, i.e., an element of Nat. *)
ASSUME MaxNat \in Nat

(* NatOverride is the finite set of natural numbers that the module
   overrides, ranging from 0 up to MaxNat inclusive. *)
NatOverride == 0 .. MaxNat

=============================================================================