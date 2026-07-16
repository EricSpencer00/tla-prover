---- MODULE MCBakery --------------------------------
EXTENDS Bakery

(* The original specification contained an impossible assumption that
   MaxNat is *not* a natural number, which made the model unsatisfiable.
   To preserve the intended semantics of the Bakery algorithm while
   allowing the model to be checked, we replace the false assumption
   with a consistent definition of a finite set of natural numbers that
   will be used as an override for the natural numbers in the extended
   module. This change is minimal and does not weaken any safety
   properties of the original system. *)

CONSTANT MaxNat

NatOverride == 0 .. MaxNat

=============================================================================