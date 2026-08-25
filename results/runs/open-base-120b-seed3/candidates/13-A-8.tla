---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, TLC, Bakery

CONSTANT N, MaxNat

(*---------------------------------------------------------------------*)
(*  Finite version of the natural numbers set.  The .cfg file will      *)
(*  replace uses of Nat with NatOverride, limiting ticket numbers to   *)
(*  the range 0..MaxNat.                                                *)
(*---------------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*---------------------------------------------------------------------*)
(*  Specification used for model checking.  It builds on the Init and *)
(*  Next definitions provided by the Bakery module.                  *)
(*---------------------------------------------------------------------*)
ISpec == Init /\ [][Next]_vars

=============================================================================