---- MODULE MCBakery --------------------------------
EXTENDS Bakery
CONSTANT MaxNat
(* The original specification incorrectly assumed MaxNat is NOT a natural number,
   which makes the model invalid because NatOverride would then be empty.
   We replace that assumption with a correct one that states MaxNat is a natural number.
   This preserves the intended semantics: NatOverride should be a non‑empty range of natural numbers. *)
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
====