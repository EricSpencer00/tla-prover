---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Inductive specification: starts from any state satisfying the type
\* invariant and the full invariant, and then repeatedly takes steps of
\* the algorithm.
ISpec == TypeOK /\ Inv /\ [][Next]_vars

====