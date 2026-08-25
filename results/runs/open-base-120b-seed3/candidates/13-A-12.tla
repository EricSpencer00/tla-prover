---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANT N, MaxNat

\* Finite version of the natural numbers used for model checking.
NatOverride == 0 .. MaxNat

\* Inductive specification (inherits Init and Next from Bakery).
ISpec == Spec

====