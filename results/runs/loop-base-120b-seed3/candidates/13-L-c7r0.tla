---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* ----------------------------------------------------------------------
NatOverride == { n \in Nat : n <= MaxNat }

\* ----------------------------------------------------------------------
\* State variables (same as in the Bakery specification)
\* ----------------------------------------------------------------------
VARIABLES pc, ticket, choosing

\* ----------------------------------------------------------------------
\* Initial state: same as Bakery's Init, but ticket numbers are restricted
\* to the finite range NatOverride.
\* ----------------------------------------------------------------------
Init ==
    /\ Bakery!Init
    /\ \A p \in Proc: ticket[p] \in NatOverride

\* ----------------------------------------------------------------------
\* Next-state relation: inherits all actions from Bakery.
\* ----------------------------------------------------------------------
Next ==
    /\ Bakery!Next
    /\ \A p \in Proc: ticket[p] \in NatOverride

\* ----------------------------------------------------------------------
\* Tuple of all state variables (used for stuttering)
\* ----------------------------------------------------------------------
Vars == << pc, ticket, choosing >>

\* ----------------------------------------------------------------------
\* Specification used for model checking (inductive specification).
\* ----------------------------------------------------------------------
ISpec ==
    Init /\ [][Next]_Vars

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file.
\* They are simply reused from the original Bakery specification.
\* ----------------------------------------------------------------------
MutualExclusion == Bakery!MutualExclusion
TypeOK           == Bakery!TypeOK
Inv              == Bakery!Inv

=============================================================================