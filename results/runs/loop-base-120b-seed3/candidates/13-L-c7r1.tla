---- MODULE MCBakery ----
EXTENDS Naturals, Bakery

CONSTANTS N, MaxNat

\* ----------------------------------------------------------------------
\* Finite version of the natural numbers used for model checking.
\* ----------------------------------------------------------------------
NatOverride == { n \in Nat : n <= MaxNat }

\* ----------------------------------------------------------------------
\* State‑space restriction: ticket numbers must stay within NatOverride.
\* ----------------------------------------------------------------------
BoundedTicket == \A p \in Proc : ticket[p] \in NatOverride

\* ----------------------------------------------------------------------
\* Tuple of all state variables (used for stuttering).
\* ----------------------------------------------------------------------
Vars == << pc, ticket, choosing >>

\* ----------------------------------------------------------------------
\* Specification used for model checking (inductive specification).
\* ----------------------------------------------------------------------
ISpec ==
    /\ Bakery!Init
    /\ BoundedTicket
    /\ [][ /\ Bakery!Next /\ BoundedTicket ]_Vars

============================================================================