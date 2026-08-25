---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* The original infinite Nat is kept unchanged; NatOverride is used in
\* the type invariants to restrict ticket numbers.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Re‑expose the core operators of the original Bakery specification.
\* ----------------------------------------------------------------------
Init == Bakery.Init
Next == Bakery.Next

\* ----------------------------------------------------------------------
\* Tuple of all state variables defined in the Bakery specification.
\* Adjust the list if the underlying specification uses a different set.
\* ----------------------------------------------------------------------
Vars == << pc, ticket, choosing >>

\* ----------------------------------------------------------------------
\* Inductive specification: any state satisfying TypeOK is a valid start,
\* and the system must forever respect the transition relation Next.
\* ----------------------------------------------------------------------
ISpec == TypeOK /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Invariants inherited from the Bakery specification.
\* ----------------------------------------------------------------------
MutualExclusion == Bakery.MutualExclusion
TypeOK == Bakery.TypeOK
Inv == Bakery.Inv

=============================================================================