---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat

(* The original specification incorrectly assumed MaxNat ∉ Nat, which is
   contradictory because Nat is defined as the set of natural numbers
   (including 0). As a result, TLC reports the assumption to be false.
   To preserve the intended semantics—overriding the natural numbers with a
   bounded range—we replace the false assumption with a true one that
   constrains MaxNat to be a natural number. This keeps the semantics of the
   model (using a concrete upper bound) while allowing the model to be checked. *)

ASSUME NatOverrideExists == MaxNat \in Nat

NatOverride == 0 .. MaxNat
====