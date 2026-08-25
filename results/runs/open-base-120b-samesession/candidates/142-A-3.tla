---- MODULE ReachableProofs ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Edge

\* ----------------------------------------------------------------------
\* State variables of the sequential Misra reachability algorithm
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Succ(n) == { m \in Nodes : <<n, m>> \in Edge }

Reachable(S) == TC(Edge, S)   \* transitive closure of the edge relation

\* ----------------------------------------------------------------------
\* INITIAL STATE (INIT)
\* ----------------------------------------------------------------------
INIT ==
    /\ marked   = {Root}
    /\ frontier = {}
    /\ pc       = "init"

\* ----------------------------------------------------------------------
\* NEXT STATE RELATION (NEXT)
\* ----------------------------------------------------------------------
NEXT ==
    \/ /\ pc = "init"
       /\ pc' = "run"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "run"
       /\ frontier # {}
       /\ LET n == CHOOSE x \in frontier : TRUE
          IN /\ marked'   = marked \cup {n}
             /\ frontier' = (frontier \ {n}) \cup { s \in Nodes : s \in Succ[n] }
             /\ pc'       = IF frontier' = {} THEN "done" ELSE "run"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* INVARIANTS
\* ----------------------------------------------------------------------
\* Invariant 1: type correctness and successor condition
Inv1 ==
    /\ marked   \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ \A n \in marked :
         \A s \in Succ(n) : s \in marked \/ s \in frontier

\* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier)
Inv2 ==
    (marked \cup Reachable(frontier)) = Reachable(marked \cup frontier)

\* Invariant 3: Reachable({Root}) = marked ∪ Reachable(frontier) at termination
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

INVARIANTS == /\ Inv1 /\ Inv2 /\ Inv3

\* ----------------------------------------------------------------------
\* SPECIFICATION (Spec)
\* ----------------------------------------------------------------------
Spec == INIT /\ [][NEXT]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* PROPERTIES (theorems to be checked)
\* ----------------------------------------------------------------------
PROPERTIES == []INVARIANTS

=============================================================================