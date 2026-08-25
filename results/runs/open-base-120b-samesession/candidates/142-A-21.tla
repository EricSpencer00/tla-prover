---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, 
        SeqReachAlg,          \* the sequential reachability algorithm module
        ReachabilityLemmas    \* the module containing the graph‑theoretic lemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\*  Initial state (unspecified in the description – left as TRUE)
\* ----------------------------------------------------------------------
Init == TRUE

\* ----------------------------------------------------------------------
\*  Next-state relation (unspecified – left as TRUE)
\* ----------------------------------------------------------------------
Next == TRUE

\* ----------------------------------------------------------------------
\*  Invariant 1 : type correctness and successor condition
\* ----------------------------------------------------------------------
Inv1 == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
          \A m \in Succ(n) :   \* Succ is supplied by ReachabilityLemmas
              m \in marked \/ m \in frontier

\* ----------------------------------------------------------------------
\*  Invariant 2 : relationship between marked, frontier and reachability
\* ----------------------------------------------------------------------
Inv2 == 
    marked \cup ReachableFrom(frontier) 
        = ReachableFrom(marked \cup frontier)   \* ReachableFrom is supplied by ReachabilityLemmas

\* ----------------------------------------------------------------------
\*  Invariant 3 : marked set equals reachable set from the root
\* ----------------------------------------------------------------------
Inv3 == 
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* ----------------------------------------------------------------------
\*  Collection of all invariants
\* ----------------------------------------------------------------------
INVARIANTS == /\ Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\*  Properties to be checked (here we expose the invariants)
\* ----------------------------------------------------------------------
PROPERTIES == INVARIANTS

\* ----------------------------------------------------------------------
\*  The full specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>
Spec == Init /\ [][Next]_vars

=============================================================================