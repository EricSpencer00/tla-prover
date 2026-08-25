---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

(*-----------------------------------------------------------------
  Finite version of the natural numbers used for model checking.
  The .cfg file will replace occurrences of Nat with NatOverride.
-----------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*-----------------------------------------------------------------
  Inductive specification: any state satisfying the type invariant
  and the inductive invariant may be taken as an initial state.
-----------------------------------------------------------------*)
ISpec == (Init \/ (TypeOK /\ Inv)) /\ [][Next]_vars

====