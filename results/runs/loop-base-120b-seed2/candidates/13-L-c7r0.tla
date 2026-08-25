---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* Finite version of the natural numbers for model checking
NatOverride == 0 .. MaxNat

\* Tuple of the state variables defined in the Bakery specification
vars == <<pc, number, flag>>

\* Inductive specification: any state satisfying the invariant is a legal start,
\* and all steps must follow the Next action of the Bakery algorithm.
ISpec == Inv /\ [][Next]_vars

====