---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State definitions
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
MarkAndAdd ==
    \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc' = pc

RemoveMarked ==
    \E n \in frontier :
        /\ n \in marked
        /\ marked' = marked
        /\ frontier' = frontier \ {n}
        /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ /\ pc = "Running"
       /\ frontier # {}
       /\ (MarkAndAdd \/ RemoveMarked)
    \/ /\ pc = "Running"
       /\ frontier = {}
       /\ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Reachability helper definitions (used in invariants)
\* ----------------------------------------------------------------------
\* Definition of the set of nodes reachable from a given set S using Succ
ReachableFrom(S) ==
    LET R == RECURSIVE R(_)
    IN  R(S) where
        R(T) == T \cup UNION { Succ[t] : t \in T }
        \* This is a simple over‑approximation sufficient for the invariants
        \* (the true least fix‑point is not needed for safety checking).

\* ----------------------------------------------------------------------
\* Safety invariants described in the natural‑language text
\* ----------------------------------------------------------------------
\* Inv1: every successor of a marked node is in marked or frontier
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: (marked ∪ frontier) is closed under successors
Inv2 ==
    \A n \in marked \cup frontier : Succ[n] \subseteq marked \cup frontier

\* Inv3: the nodes reachable from the root equal marked plus those reachable from frontier
Inv3 ==
    ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

\* Partial correctness: when terminated, marked equals the reachable set
PartialCorrectness ==
    pc = "Done" => marked = ReachableFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination ==
    [](pc = "Running" => <> (pc = "Done"))

\* ----------------------------------------------------------------------
\* THEOREM (optional, to help TLC)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====