---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences
EXTENDS SeqReachAlg, GraphLemmas \* modules providing the algorithm definition and graph lemmas

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State variable types
\* ----------------------------------------------------------------------
TypeInvariant ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"init", "step", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
\* ----------------------------------------------------------------------
Invariant1 ==
    /\ TypeInvariant
    /\ \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: relationship between marked/frontier and reachability
\* ----------------------------------------------------------------------
Invariant2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: marked set equals reachable set from the root
\* ----------------------------------------------------------------------
Invariant3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

\* ----------------------------------------------------------------------
\* Initial state (delegated to the algorithm module if available)
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "init"

\* ----------------------------------------------------------------------
\* Next-state relation (placeholder – actual algorithm steps are in SeqReachAlg)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "init"
       /\ pc' = "step"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "step"
       /\ \* algorithm step (details omitted)
          TRUE
       /\ UNCHANGED pc
    \/ /\ pc = "step"
       /\ \* termination condition (details omitted)
          TRUE
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Collection of invariants for the model checker
\* ----------------------------------------------------------------------
Invariants ==
    <<Invariant1, Invariant2, Invariant3>>

\* ----------------------------------------------------------------------
\* Properties (theorem of partial correctness)
\* ----------------------------------------------------------------------
Properties ==
    <<\* When the algorithm terminates, the marked set equals the reachable set
       THEOREM == 
          /\ [] (pc = "done" => marked = Reachable({Root}))
    >>

====