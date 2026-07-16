---- MODULE MCBakery ----
(* 
  The original specification attempted to assume that MaxNat is not a natural number,
  then defined NatOverride as the interval 0..MaxNat.  This makes the assumption
  contradictory because if MaxNat is not in Nat, the interval 0..MaxNat is empty,
  which would likely break the intended model.  To preserve the intended semantics
  (that MaxNat should be a natural number that bounds the NatOverride range) we
  replace the contradictory assumption with a correct one: MaxNat is a natural
  number.  This change is minimal, does not delete any existing definitions, and
  keeps the rest of the specification unchanged.
*)

EXTENDS Bakery
CONSTANT MaxNat

(* MaxNat must be a natural number, i.e., a non‑negative integer. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat

=============================================================================