---- MODULE MCBakery --------------------------------
EXTENDS Bakery

(* A small finite set of natural numbers that we will use for the
   NatOverride constant. The set must be non‑empty to avoid a vacuous
   model. *)
NatOverride == 0 .. 1

=============================================================================