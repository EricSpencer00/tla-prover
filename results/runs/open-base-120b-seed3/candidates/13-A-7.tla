---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(*--------------------------------------------------------------------*)
(*  Finite override for the (infinite) set of natural numbers.        *)
(*--------------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*--------------------------------------------------------------------*)
(*  Inductive specification: any type‑correct state satisfying the    *)
(*  invariant may be a starting point, and the system must always    *)
(*  respect the actions of the original Bakery specification.        *)
(*--------------------------------------------------------------------*)
ISpec == Init /\ [][Next]_vars

=============================================================================