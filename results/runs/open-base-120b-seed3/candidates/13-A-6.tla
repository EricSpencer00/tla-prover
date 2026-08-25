---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(*--------------------------------------------------------------------
  Finite replacement for the infinite set Nat.
  The configuration file will replace Nat with NatOverride.
--------------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*--------------------------------------------------------------------
  Inductive specification: any state satisfying the type invariant
  and the full invariant, and all steps preserve the invariant.
--------------------------------------------------------------------*)
ISpec ==
    /\ TypeOK
    /\ Inv
    /\ [][Next]_vars

====