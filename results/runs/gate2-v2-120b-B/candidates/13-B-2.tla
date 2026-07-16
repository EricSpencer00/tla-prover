---------------------------- MODULE MCBakery --------------------------------
EXTENDS Bakery
CONSTANT MaxNat

(* This assumption is changed so that the module is consistent with the
   semantics of the extended Naturals module.  MaxNat must be a natural
   number (including 0). *)
ASSUME MaxNat \in Nat

NatOverride == 0 .. MaxNat
=============================================================================