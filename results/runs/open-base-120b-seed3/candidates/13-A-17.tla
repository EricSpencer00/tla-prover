---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

(*-----------------------------------------------------------------
  Finite version of the natural numbers used by the model checker.
  The .cfg file will substitute Nat with NatOverride, so all uses of
  Nat in the imported Bakery module will be interpreted as this
  finite set.
-----------------------------------------------------------------*)
NatOverride == 0 .. MaxNat

(*-----------------------------------------------------------------
  State variables – the same as in the Bakery specification.
-----------------------------------------------------------------*)
VARIABLES pc, ticket, choosing

(*-----------------------------------------------------------------
  Initialization and next-state relation are taken directly from the
  Bakery specification (which uses the overridden Nat).
-----------------------------------------------------------------*)
Init == Bakery!Init
Next == Bakery!Next

(*-----------------------------------------------------------------
  Invariants and safety properties inherited from the Bakery spec.
-----------------------------------------------------------------*)
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv
MutualExclusion == Bakery!MutualExclusion

(*-----------------------------------------------------------------
  Inductive specification: any state satisfying TypeOK and Inv is
  admissible, and all steps must follow Next.
-----------------------------------------------------------------*)
ISpec == (TypeOK /\ Inv) /\ [][Next]_<<pc, ticket, choosing>>

====