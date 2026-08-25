---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Helper operator used by the .cfg substitution:
\*   ConnectedToSomeButNotAll replaces Succ in the model.
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == {}  \* placeholder; the .cfg will supply a concrete definition

\* ----------------------------------------------------------------------
\* A finite version of Seq for model checking (replaces Seq via .cfg)
\* ----------------------------------------------------------------------
CONSTANT MaxLen \* a bound on sequence length; can be set in the .cfg
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Edge relation of the graph (as a set of ordered pairs)
\* ----------------------------------------------------------------------
Edge == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

\* ----------------------------------------------------------------------
\* Reachability from a set of nodes (including the nodes themselves)
\* ----------------------------------------------------------------------
Reach(S) == S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(Edge) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Main action: pick a node from the frontier and process it
\* ----------------------------------------------------------------------
PickNode ==
    \E n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = pc
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = pc

\* ----------------------------------------------------------------------
\* Termination action: when the frontier is empty
\* ----------------------------------------------------------------------
Terminate ==
    /\ frontier = {}
    /\ pc = "Run"
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ PickNode
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is either marked or in the frontier
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: reachable from (marked ∪ frontier) equals marked ∪ reachable from frontier
\* ----------------------------------------------------------------------
Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: reachable from the root equals marked ∪ reachable from frontier
\* ----------------------------------------------------------------------
Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when the algorithm has terminated, marked = reachable from root
\* ----------------------------------------------------------------------
PartialCorrectness ==
    pc = "Done" => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination (when reachable set is finite)
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

====