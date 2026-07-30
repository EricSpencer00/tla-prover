---- MODULE ReachableProofs ----
EXTENDS Reachable, ReachabilityLemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "running"

Explore ==
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Succ(n) \ marked)
    /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc = "running"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

\* Invariant 1 is the core inductive property: every successor of a marked
\* node is already marked or in the frontier.
MarkingIsLocalized ==
    /\ TypeOK
    /\ \A n \in marked : Succ(n) \subseteq (marked \cup frontier)

\* Invariant 2 follows directly from Lemma 1 in ReachabilityLemmas.
FromMarkedOrFrontier ==
    ReachedFrom(marked) \cup ReachedFrom(frontier) = ReachedFrom(marked \cup frontier)

\* Invariant 3 follows from Lemmas 2 and 3 in ReachabilityLemmas.
MarkedEqualsReachable ==
    ReachedFrom(Root) = marked \cup ReachedFrom(frontier)

INVARIANTS == MarkingIsLocalized /\ FromMarkedOrFrontier /\ MarkedEqualsReachable

\* TLAPS proves the partial correctness theorem below; it is not a
\* separate invariant. Termination itself is not proved.
PartialCorrectness ==
    (pc = "done") => (marked = ReachedFrom(Root))

PROPERTIES == PartialCorrectness
====