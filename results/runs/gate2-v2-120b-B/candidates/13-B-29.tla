---- MODULE MCBakery --------------------------------
EXTENDS Bakery
CONSTANT MaxNat
(* 
  The original specification assumed that MaxNat is *not* a natural
  number, which immediately contradicts the definition of NatOverride
  (a set of natural numbers up to MaxNat) and causes TLC to abort.
  To preserve the intended meaning—namely, that MaxNat bounds the
  natural numbers used by the Bakery module—we replace the false
  assumption with a correct one that states MaxNat is a natural
  number.  This change is minimal and does not weaken any invariants
  or properties of the underlying Bakery specification.
*)
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
=============================================================================