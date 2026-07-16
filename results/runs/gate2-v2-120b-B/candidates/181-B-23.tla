------------------------ MODULE MC_sums_even -----------------------
EXTENDS sums_even
CONSTANT MaxNat
(* The original specification incorrectly assumed that MaxNat is not a natural
   number, which makes the model impossible to satisfy.  We replace that
   assumption with a constraint that MaxNat is a natural number within the
   range of the Naturals module.  This preserves the intended meaning that
   MaxNat bounds the overridden natural numbers, while allowing the model to
   be instantiated. *)
ASSUME MaxNat \in Nat
NatOverride == 0 .. MaxNat
ASSUME T1
=============================================================================