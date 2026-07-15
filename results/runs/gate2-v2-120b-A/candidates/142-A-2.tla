---- MODULE ReachableProofs ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS Nodes, Root

VARIABLES marked, frontier, pc

\* ==================================================================
\* Basic definitions
\* ==================================================================
Reachable(s) == 
    { n \in Nodes : \E p \in Seq(Node) : 
        Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = n /\ 
        \A i \in 1..(Len(p)-1) : (p[i] , p[i+1]) \in E }

\* Assume the graph edges are given as a constant relation E
CONSTANT E

\* ==================================================================
\* Initial state
\* ==================================================================
Init ==
    /\ marked = {Root}
    /\ frontier = {}
    /\ pc = "Start"

\* ==================================================================
\* Actions (only the ones needed for the invariants)
\* ==================================================================
AddFrontier ==
    /\ pc = "Start"
    /\ frontier' = { n \in Nodes : \E m \in marked : (m, n) \in E /\ n \notin marked }
    /\ marked' = marked
    /\ pc' = "Propagate"

Propagate ==
    /\ pc = "Propagate"
    /\ \E n \in frontier :
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \ {n}
        /\ pc' = "Propagate"
    \/ /\ frontier = {}
       /\ pc' = "Done"
    /\ UNCHANGED <<>>

Next ==
    \/ AddFrontier
    \/ Propagate

\* ==================================================================
\* Specification
\* ==================================================================
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ==================================================================
\* Invariant 1: type correctness + successor condition
\* ==================================================================
Inv1 ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Start", "Propagate", "Done"}
    /\ \A m \in marked :
          \A s \in Nodes :
            (m, s) \in E => (s \in marked) \/ (s \in frontier)

\* ==================================================================
\* Invariant 2: marked ∪ Reachable(frontier) = Reachable(marked ∪ frontier)
\* ==================================================================
Inv2 ==
    marked \cup Reachable(frontier) = Reachable(marked \cup frontier)

\* ==================================================================
\* Invariant 3: Reachable(Root) = marked ∪ Reachable(frontier)
\* ==================================================================
Inv3 ==
    Reachable({Root}) = marked \cup Reachable(frontier)

\* ==================================================================
\* Theorem: partial correctness upon termination
\* ==================================================================
TerminationTheorem == 
    pc = "Done" => marked = Reachable({Root})

\* The configuration file expects the following names:
\*   SPECIFICATION formula: Spec
\*   INVARIANT 1: Inv1
\*   INVARIANT 2: Inv2
\*   INVARIANT 3: Inv3
\*   THEOREM   : TerminationTheorem

====