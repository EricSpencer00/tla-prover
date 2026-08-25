---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* The set of all graph nodes
    Root,           \* The distinguished start node
    Succ            \* Successor function: [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Operators overridden by the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* A finite version of Seq (used by the model checker)
\* ----------------------------------------------------------------------
LimitedSeq(S) == Seq(S) /\ Finite(S)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    marked,   \* set of nodes that have been visited
    frontier, \* set of nodes pending exploration (may overlap with marked)
    pc        \* program counter: "run" or "done"

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Relation induced by Succ
R == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

\* Nodes reachable from a set of start nodes (including the start nodes)
Reach(S) == S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(R) }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
PickUnmarked ==
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
          /\ UNCHANGED pc

PickMarked ==
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ UNCHANGED marked
          /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED marked

StutterDone ==
    /\ pc = "done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next ==
    \/ PickUnmarked
    \/ PickMarked
    \/ Terminate
    \/ StutterDone

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    pc = "done" => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination ==
    (Finite(Reach({Root})) => <> (pc = "done"))

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* SPECIFICATION formula
Spec

\* INVARIANTS list
TypeOK
Inv1
Inv2
Inv3
PartialCorrectness

\* PROPERTIES list
Termination

====