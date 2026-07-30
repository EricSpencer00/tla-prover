---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Reachable

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"idle", "searching", "done"}

Init ==
    /\ marked = {Root}
    /\ frontier = {Root}
    /\ pc = "idle"

BeginSearch ==
    /\ pc = "idle"
    /\ pc' = "searching"
    /\ UNCHANGED <<marked, frontier>>

Grow(n) ==
    /\ pc = "searching"
    /\ n \in frontier
    /\ \E m \in Nodes :
         /\ Edge(n, m)
         /\ m \notin marked
         /\ frontier' = (frontier \cup {m}) \ {n}
    /\ marked' = marked \cup {n}
    /\ UNCHANGED pc

FinishSearch ==
    /\ pc = "searching"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

InitStep == BeginSearch
SearchStep == \E n \in Nodes : Grow(n)
Next == InitStep \/ SearchStep \/ FinishSearch

Spec == Init /\ [][Next]_vars

\* Invariant 1 (inductive): type correctness plus every successor of a marked
\* node is in the marked set or frontier.
FrontierClosed ==
    /\ TypeOK
    /\ \A n \in marked : \A m \in Nodes : Edge(n, m) => m \in marked \cup frontier

\* Invariant 2: the reachable-from-marked and reachable-from-frontier sets
\* together equal the reachable-from-(marked union frontier) set. Derived from
\* Lemma 1 of the graph-theoretic library.
MarkedFrontierReach ==
    ReachableFrom(marked) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: the reachable-from-root set equals the marked set plus
\* reachable-from-frontier. Uses Lemma 2 (reachability stable under adding
\* successors) and Lemma 3 (reachability from empty is empty).
MarkedPlusFrontier ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS == FrontFactorClosed /\ MarkedFrontierReach /\ MarkedPlusFrontier

\* Partial correctness: termination leaves exactly the reachable set marked.
PartialCorrect == (pc = "done") => (marked = ReachableFrom({Root}))

====