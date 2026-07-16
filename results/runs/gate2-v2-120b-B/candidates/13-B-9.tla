---- MODULE MCBakery ----
EXTENDS Bakery

CONSTANT MaxNat

(* The original specification incorrectly assumed MaxNat ∉ Nat, which makes the
   model unsatisfiable because Nat is the set of all natural numbers and
   MaxNat is a constant that must denote a natural number.  The intended
   constraint is that MaxNat is a natural number that serves as an upper
   bound for the overridden natural-number set NatOverride.  We replace the
   false assumption with a correct one that preserves the intended semantics. *)

ASSUME NatOverride = 0 .. MaxNat

=============================================================================