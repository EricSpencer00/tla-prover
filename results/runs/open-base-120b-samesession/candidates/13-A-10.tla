---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Tuple of all state variables (as defined in the Bakery module)
Vars == << pc, ticket, choosing >>

\* Inductive specification: any type‑correct state satisfying the invariant may be initial,
\* and the system repeatedly executes Next while preserving the invariant.
ISpec == (TypeOK /\ Inv) /\ [][Next]_Vars
====