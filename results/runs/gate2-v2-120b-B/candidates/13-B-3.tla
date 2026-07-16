---- MODULE MCBakery ----
EXTENDS Bakery

CONSTANT MaxNat

(* Ensure MaxNat is a natural number that is not zero. *)
ASSUME MaxNat \in Nat \ {0}

NatOverride == 0 .. MaxNat

====