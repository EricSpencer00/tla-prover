---- MODULE MCBakery ----
EXTENDS Bakery

CONSTANT MaxNat

(* MaxNat must be a natural number (including zero) *)
ASSUME MaxNat \in Nat

(* NatOverride is the set of natural numbers up to MaxNat *)
NatOverride == 0 .. MaxNat

=============================================================================