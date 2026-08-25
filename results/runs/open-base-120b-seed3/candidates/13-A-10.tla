---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* -----------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* The .cfg file will replace Nat with NatOverride.
\* -----------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* -----------------------------------------------------------------
\* Inductive specification: start from any state that satisfies the
\* type invariants and the full invariant, then allow any number of
\* Next steps.
\* -----------------------------------------------------------------
ISpec ==
    /\ TypeOK
    /\ Inv
    /\ [][Next]_vars

====