---------------------------- MODULE MCBakery --------------------------------
EXTENDS Bakery

(* The constant MaxNat is used as the exclusive upper bound of the range
   NatOverride.  To avoid a false assumption, we assume that MaxNat is a
   natural number (i.e., MaxNat ∈ Nat) and then define NatOverride as the
   set of natural numbers strictly less than MaxNat.  This preserves the
   intended meaning of NatOverride while ensuring the assumption can be
   satisfied. *)

CONSTANT MaxNat
ASSUME MaxNat ∈ Nat

NatOverride == 0 .. (MaxNat - 1)

=============================================================================