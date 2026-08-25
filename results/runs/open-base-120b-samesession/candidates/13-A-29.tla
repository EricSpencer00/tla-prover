---- MODULE MCBakery ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* It replaces the infinite set Nat from the Naturals module.
\* ----------------------------------------------------------------------
NatOverride == 0 .. MaxNat

\* ----------------------------------------------------------------------
\* Include the original Bakery specification.  All of its definitions
\* (variables, actions, invariants, etc.) become available in this
\* module.
\* ----------------------------------------------------------------------
INSTANCE Bakery

\* ----------------------------------------------------------------------
\* Tuple of all state variables defined by the Bakery module.
\* Adjust this definition if the Bakery specification uses a different
\* set of variables.
\* ----------------------------------------------------------------------
Vars == << flag, number >>

\* ----------------------------------------------------------------------
\* Inductive specification used for model checking.
\* It starts from any type‑correct state (i.e., a state satisfying
\* the TypeOK invariant) and requires that every transition preserves
\* the Next relation.
\* ----------------------------------------------------------------------
ISpec == TypeOK /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* The required invariants are already provided by the Bakery module:
\*   MutualExclusion  – no two processes are in the critical section
\*   TypeOK           – all variables have values in their intended sets
\*   Inv              – the full inductive invariant of the algorithm
\* They are therefore simply exported unchanged.
\* ----------------------------------------------------------------------
\* (No additional definitions are needed; the identifiers are
\*   available through the INSTANCE above.)

====