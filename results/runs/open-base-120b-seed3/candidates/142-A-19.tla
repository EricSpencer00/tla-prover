---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants required by the configuration
\* ----------------------------------------------------------------------
CONSTANTS Nodes, Root

\* (Optional) the graph edge relation; can be instantiated by the caller
CONSTANT Edge \in [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* State variables of the sequential reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of nodes reachable from a given set S via the Edge relation
ReachFrom(S) ==
    LET R == RECURSIVE R(_)
    IN  R(S) = 
        IF S = {} THEN {} 
        ELSE S \cup R({ n \in Nodes : \E m \in S : n \in Edge[m] })
    IN  R(S)

\* The set of all nodes reachable from the root
ReachableRoot == ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Initial state (type-correctness and empty markings)
\* ----------------------------------------------------------------------
Init ==
    /\ marked \in SUBSET Nodes
    /\ frontier \in SUBSET Nodes
    /\ pc \in {"init", "run", "done"}
    /\ marked = {}
    /\ frontier = {}
    /\ pc = "init"

\* ----------------------------------------------------------------------
\* Actions (placeholder definitions sufficient for the specification)
\* ----------------------------------------------------------------------
AddFrontier ==
    /\ pc = "init"
    /\ frontier' = {Root}
    /\ marked' = {}
    /\ pc' = "run"
    /\ UNCHANGED marked

ProcessFrontier ==
    /\ pc = "run"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = (frontier \ {n}) \cup (Edge[n] \ (marked \cup frontier))
        /\ UNCHANGED pc

Done ==
    /\ pc = "run"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ AddFrontier
    \/ ProcessFrontier
    \/ Done

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor property
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A m \in marked :
          Edge[m] \subseteq marked \cup frontier

\* Invariant 2: marked ∪ ReachFrom(frontier) = ReachFrom(marked ∪ frontier)
Inv2 ==
    marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

\* Invariant 3: ReachableRoot = marked ∪ ReachFrom(frontier)
Inv3 ==
    ReachableRoot = marked \cup ReachFrom(frontier)

Invariants ==
    /\ Inv1
    /\ Inv2
    /\ Inv3

\* ----------------------------------------------------------------------
\* Properties (partial correctness theorem)
\* ----------------------------------------------------------------------
\* When the algorithm terminates (pc = "done"), the marked set equals the
\* set of nodes reachable from the root.
PartialCorrectness ==
    /\ pc = "done"
    => marked = ReachableRoot

Properties ==
    PartialCorrectness

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

====