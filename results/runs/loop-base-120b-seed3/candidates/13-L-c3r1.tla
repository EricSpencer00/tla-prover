---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking
NatOverride == 0 .. MaxNat

\* Export the invariants defined in the Bakery module so that the
\* configuration (.cfg) file can refer to them directly.
MutualExclusion == Bakery!MutualExclusion
TypeOK == Bakery!TypeOK
Inv == Bakery!Inv

\* Inductive specification: starts from any state satisfying the type
\* invariant and the full invariant, and then repeatedly takes steps of
\* the algorithm.
ISpec == TypeOK /\ Inv /\ [][Next]_vars

====