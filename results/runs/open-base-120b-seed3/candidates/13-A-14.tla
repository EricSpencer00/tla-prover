---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Inductive specification: starts from any type‑correct state and
\* stays within the transition relation Next.
ISpec == TypeOK /\ [][Next]_(<<pc, ticket, choosing>>)

====