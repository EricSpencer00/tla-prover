---- MODULE ReachableProofs ----
EXTENDS SeqReachabilityAlg, ReachabilityLemmas

CONSTANTS
    Nodes,      \* the set of all nodes in the graph
    Root        \* the distinguished start node

VARIABLES
    marked,     \* the set of nodes that have been permanently marked
    frontier,   \* the set of nodes that are currently on the frontier
    pc          \* program counter of the sequential algorithm

\* ----------------------------------------------------------------------
\* State vector used by the temporal operator [][Next]_vars
vars == << marked, frontier, pc >>

\* ----------------------------------------------------------------------
\* Initial state (as defined by the underlying algorithm module)
Init == InitAlg   \* InitAlg is exported by SeqReachabilityAlg

\* ----------------------------------------------------------------------
\* Next-state relation (as defined by the underlying algorithm module)
Next == NextAlg   \* NextAlg is exported by SeqReachabilityAlg

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor property
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"start", "step", "done"}  \* placeholder for the algorithm's control states
    /\ \A v \in marked :
          \A w \in Succ(v) :           \* Succ is exported by SeqReachabilityAlg
              w \in marked \/ w \in frontier

\* ----------------------------------------------------------------------
\* Invariant 2: relation between marked, frontier and reachable sets
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)
    \* ReachableFrom is exported by ReachabilityLemmas

\* ----------------------------------------------------------------------
\* Invariant 3: marked set together with frontier reachability equals full reachability
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* ----------------------------------------------------------------------
\* Collection of invariants required by the configuration file
INVARIANTS == { Inv1, Inv2, Inv3 }

\* ----------------------------------------------------------------------
\* Partial‑correctness theorem: when the algorithm terminates,
\* the set of marked nodes equals the set of nodes reachable from the root.
PartialCorrectness ==
    [] (pc = "done") => marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Property list required by the configuration file
PROPERTIES == PartialCorrectness

====