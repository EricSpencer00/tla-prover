---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, ReachabilityLemmas

CONSTANTS
    Nodes,      \* The set of all graph nodes
    Root        \* The distinguished start node

\* (Optional) graph edge relation; assumed to be provided by the extended modules
CONSTANT Edges \* Subset of Nodes \X Nodes

VARIABLES
    marked,     \* set of nodes already marked as reachable
    frontier,   \* set of nodes on the current frontier
    pc          \* program counter (one of "Init", "Run", "Done")

\* Helper definition: successors of a node according to Edges
Succ(n) == { m \in Nodes : <<n, m>> \in Edges }

\* ----------------------------------------------------------------------
\* INITIAL STATE (INIT)
\* ----------------------------------------------------------------------
INIT ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Init"

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION (NEXT)
\* ----------------------------------------------------------------------
NEXT ==
    \/ /\ pc = "Init"
       /\ pc' = "Run"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Run"
       /\ \* A generic transition that may add successors of the frontier
          \* to the marked set and compute a new frontier.
          \E newMarked, newFrontier :
              /\ newMarked   \subseteq Nodes
              /\ newFrontier \subseteq Nodes
              /\ marked'   = marked \cup newMarked
              /\ frontier' = newFrontier
              /\ pc'       = IF newFrontier = {} THEN "Done" ELSE "Run"
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* INVARIANTS
\* ----------------------------------------------------------------------
Inv1 ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Init", "Run", "Done"}
    /\ \A n \in marked : Succ(n) \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

INVARIANTS == Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\* PROPERTIES (partial‑correctness theorem)
\* ----------------------------------------------------------------------
PROPERTIES ==
    (pc = "Done") => (marked = ReachFrom({Root}))

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec ==
    /\ INIT
    /\ [][NEXT]_(<<marked, frontier, pc>>)
    /\ INVARIANTS

====