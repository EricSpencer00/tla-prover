---- MODULE ReachableProofs ----
EXTENDS SeqReachability, ReachabilityLemmas, Naturals

CONSTANTS
    Nodes, \* The set of all nodes in the graph
    Root   \* The distinguished start node

VARIABLES
    marked,   \* Set of nodes already marked as reachable
    frontier, \* Set of nodes whose successors are to be explored
    pc        \* Program counter representing the current phase

\* ----------------------------------------------------------------------
\* State space
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial state (taken from the underlying algorithm)
\* ----------------------------------------------------------------------
INIT ==
    /\ marked   = {}
    /\ frontier = {Root}
    /\ pc       = "Expand"

\* ----------------------------------------------------------------------
\* Transition relation (again, delegating to the algorithmic definition)
\* ----------------------------------------------------------------------
NEXT ==
    \/ /\ pc = "Expand"
       /\ frontier # {}                                   \* there is work to do
       /\ LET n == Choose(frontier) IN
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n})
                         \cup { m \in Nodes : <<n, m>> \in Edges }
          /\ pc'       = "Expand"
    \/ /\ pc = "Expand"
       /\ frontier = {}                                   \* no more nodes to explore
       /\ pc'       = "Done"
       /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    INIT /\ [][NEXT]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
TypeInvariant ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
          \A m \in Nodes :
              <<n, m>> \in Edges => (m \in marked \/ m \in frontier)

\* Invariant 2: relationship between marked, frontier and reachability
Inv2 ==
    marked \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Invariant 3: marked set together with frontier reachability equals
\*            the reachability from the root
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

INVARIANTS ==
    /\ TypeInvariant
    /\ Inv2
    /\ Inv3

\* ----------------------------------------------------------------------
\* Safety property (partial correctness)
\* ----------------------------------------------------------------------
\* When the algorithm terminates (pc = "Done") the set of marked nodes
\* equals the set of nodes reachable from the root.
PartialCorrectness ==
    [] (pc = "Done" => marked = ReachableFrom({Root}))

PROPERTIES ==
    PartialCorrectness

====