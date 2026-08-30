---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachesDefs

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

Vars == <<marked, frontier, pc>>

\* The reachable-from relation is defined in the shared graph module; a node
\* is reachable from a set if it is reachable from some member of that set.
ReachableFrom(S) == UNION {ReachableFrom(n) : n \in S}

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "first", "idle", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "start"

\* The first expansion in this sequential version is also the GC: it reuses
\* the frontier as the new marked set, so the GC step and the first expand
\* below are alternatives rather than distinct steps.
FirstExpand ==
    /\ pc = "start"
    /\ marked' = frontier
    /\ frontier' = Succ({Root})
    /\ pc' = "first"

Expand ==
    /\ pc = "idle"
    /\ marked' = marked \cup frontier
    /\ frontier' = Succ(frontier)
    /\ pc' = IF frontier = {} THEN "done" ELSE "idle"

Idle ==
    /\ pc \in {"first", "idle"}
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == FirstExpand \/ Expand \/ Idle

Spec == Init /\ [][Next]_Vars

\* Safety only: the marked set plus what can still be reached from the
\* frontier is exactly what is reachable from both together, and the
\* reachable set from the root collapses to the marked set.
Invariant1 ==
    /\ TypeOK
    /\ \A n \in marked : Succ({n}) \subseteq (marked \cup frontier)

Invariant2 ==
    ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

Invariant3 == ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == Invariant1 /\ Invariant2 /\ Invariant3

PartialCorrect == (pc = "done") => (marked = ReachableFrom({Root}))

====