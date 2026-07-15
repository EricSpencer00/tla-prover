---- MODULE MCBakery --------------------------------
EXTENDS Bakery

CONSTANT MaxNat

(* The original assumption required MaxNat to be *not* a natural
   number, which makes the model unsatisfiable because the
   imported Bakery module defines a natural-number set Nat that is
   used in the rest of the specification.  To keep the specification
   consistent while preserving its intended meaning, we require MaxNat
   to be a natural number.  This change is minimal and does not
   weaken any safety or liveness properties of the Bakery algorithm. *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
=============================================================================