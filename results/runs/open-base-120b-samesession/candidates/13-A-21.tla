---- MODULE MCBakery ----
EXTENDS Naturals, Sequences, Bakery

CONSTANT N
CONSTANT MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers set.
\* The model checker configuration will replace uses of Nat with NatOverride.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Tuple of all state variables defined in the Bakery module.
\* Adjust the list if the underlying Bakery specification uses a different
\* set of variables.
\* ----------------------------------------------------------------------
vars == <<flag, label>>

\* ----------------------------------------------------------------------
\* Inductive specification: any state satisfying the invariant may be
\* an initial state, and all executions must respect the Next action.
\* ----------------------------------------------------------------------
ISpec == Inv /\ [][Next]_vars

=============================================================================