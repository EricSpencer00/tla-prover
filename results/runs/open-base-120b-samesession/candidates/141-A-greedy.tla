---- MODULE Reachable ----
EXTENDS Naturals, Sequences

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANTS
    Nodes,   \* The set of all graph nodes
    Root,    \* The distinguished root node (Root \in Nodes)
    Succ     \* Successor function: [Nodes -> SUBSET Nodes]

\*-----------------------------------------------------------------
\* Operator substituted for Succ in the configuration
\*-----------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*-----------------------------------------------------------------
\* Finite version of Seq (used by the configuration)
\*-----------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES
    marked,   \* set of nodes that have been visited
    frontier, \* set of nodes awaiting exploration (may overlap with marked)
    pc        \* program counter: "Run" or "Done"

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
\* Reachability from a single node (transitive closure)
RECURSIVE ReachFrom(_)
ReachFrom(n) ==
    IF n \in Nodes THEN
        {n} \cup UNION { ReachFrom(m) : m \in Succ[n] }
    ELSE {}

\* Reachability from a set of nodes
ReachFromSet(F) == UNION { ReachFrom(n) : n \in F }

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Run"

\*-----------------------------------------------------------------
\* Main actions
\*-----------------------------------------------------------------
ExploreNotMarked ==
    \E n \in frontier :
        /\ n \notin marked
        /\ marked'   = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc'       = pc

ExploreAlreadyMarked ==
    \E n \in frontier :
        /\ n \in marked
        /\ marked'   = marked
        /\ frontier' = frontier \ {n}
        /\ pc'       = pc

Terminate ==
    /\ frontier = {}
    /\ pc = "Run"
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ ExploreNotMarked
    \/ ExploreAlreadyMarked
    \/ Terminate

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
vars == <<marked, frontier, pc>>

Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
TypeOK ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachFromSet(frontier) = ReachFromSet(marked \cup frontier)

Inv3 ==
    ReachFromSet({Root}) = marked \cup ReachFromSet(frontier)

PartialCorrectness ==
    frontier = {} => marked = ReachFromSet({Root})

\*-----------------------------------------------------------------
\* Liveness property
\*-----------------------------------------------------------------
Termination ==
    []<>(frontier = {})

\*-----------------------------------------------------------------
\* Exported identifiers (as required by the .cfg file)
\*-----------------------------------------------------------------
SPECIFICATION Spec
INVARIANTS TypeOK, Inv1, Inv2, Inv3, PartialCorrectness
PROPERTIES Termination

====