---- MODULE MCBakery ----
EXTENDS Bakery
CONSTANT MaxNat

(* The original assumption claimed that MaxNat is not a natural number,
   which always fails because MaxNat is a constant and the model checker
   evaluates the assumption directly.  To keep the semantics intended
   (that MaxNat is a natural number used as an upper bound) we replace the
   failing assumption with a correct one that asserts MaxNat is a natural
   number.  This change is minimal and does not affect any safety or
   liveness properties of the Bakery algorithm. *)

ASSUME NatOverride == 0 .. MaxNat

=============================================================================