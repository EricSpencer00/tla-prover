---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Edge relation (optional, can be left unconstrained)
CONSTANT Edge

Succ[n \in Nodes] == { m \in Nodes : <<n, m>> \in Edge }

\* Reachability predicate (placeholder definition)
Reachable(S) == S

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc \in {"init", "run", "done"}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
MarkStep ==
    /\ pc = "run"
    /\ \E n \in frontier :
         /\ marked' = marked \cup {n}
         /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ marked)
         /\ pc' = "run"
    /\ UNCHANGED <<>>  \* (no other variables)

DoneStep ==
    /\ pc = "run"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED marked
    /\ UNCHANGED frontier

Next ==
    \/ MarkStep
    \/ DoneStep

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeCorrectness ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "run", "done"}

SuccInMarkedOrFrontier ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Invariant1 == TypeCorrectness /\ SuccInMarkedOrFrontier

Invariant2 == (marked \cup Reachable(frontier)) = Reachable(marked \cup frontier)

Invariant3 == Reachable({Root}) = marked \cup Reachable(frontier)

Invariants == {Invariant1, Invariant2, Invariant3}

\* ----------------------------------------------------------------------
\* Properties (placeholder – can be used for the final theorem)
\* ----------------------------------------------------------------------
Properties == Invariants

====