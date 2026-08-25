---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC, SeqReachAlg, ReachabilityLemmas

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* State variables (as defined in the sequential reachability algorithm)
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definition: reachable nodes from a set of nodes using the
\* successor relation Succ.
\* ----------------------------------------------------------------------
Reachable(S) ==
  LET R ==
    RECURSIVE R(_)
    R(T) == IF T = {} THEN {}
            ELSE T \cup R({ n \in Nodes : \E m \in T : n \in Succ[m] })
  IN  R(S)

\* ----------------------------------------------------------------------
\* Initialization (mirrors the algorithm's Init)
\* ----------------------------------------------------------------------
Init ==
  /\ marked   = {}
  /\ frontier = {Root}
  /\ pc       = "start"

\* ----------------------------------------------------------------------
\* Next-state relation (mirrors the algorithm's Next)
\* ----------------------------------------------------------------------
Next ==
  \/ /\ pc = "start"
     /\ pc' = "explore"
     /\ UNCHANGED <<marked, frontier>>
  \/ /\ pc = "explore"
     /\ \E n \in frontier :
          /\ marked'   = marked \cup {n}
          /\ frontier' = (frontier \ {n}) \cup { s \in Succ[n] : s \notin marked }
          /\ pc'       = IF frontier' = {} THEN "done" ELSE "explore"
  \/ /\ pc = "done"
     /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Required identifiers
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANTS ==
  { /\ marked \subseteq Nodes
    /\ \A n \in marked : \A s \in Succ[n] : s \in marked \/ s \in frontier
  ,
    /\ marked \cup Reachable(frontier) = Reachable(marked \cup frontier)
  ,
    /\ Reachable({Root}) = marked \cup Reachable(frontier)
  }

Termination == pc = "done"

PartialCorrectness ==
  Termination => marked = Reachable({Root})

PROPERTIES == { PartialCorrectness }

====