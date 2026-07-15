---- MODULE MCBakery --------------------------------
EXTENDS Bakery

(* The constant MaxNat is intended to be an upper bound for the
   natural numbers used by the Bakery algorithm.  The original
   specification mistakenly assumed that MaxNat is *not* a natural
   number, which makes the model immediately inconsistent and
   prevents TLC from exploring any states.  The correct assumption
   is that MaxNat *is* a natural number, i.e., it belongs to Nat. *)
ASSUME MaxNat \in Nat

(* NatOverride represents the finite set of natural numbers that the
   model will use as possible ticket values.  It is defined as the
   inclusive range from 0 up to the bound MaxNat. *)
NatOverride == 0 .. MaxNat

=============================================================================