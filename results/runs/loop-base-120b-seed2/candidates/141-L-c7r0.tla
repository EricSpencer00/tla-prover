---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* Operator that the .cfg will substitute for Succ
ConnectedToSomeButNotAll == Succ

\* A finite version of Seq for model checking
MaxLen == 5
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxLen }

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Main step (Misra's variant of BFS)
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "Run"
       /\ frontier # {}
       /\ \E n \in frontier :
            \/ /\ n \notin marked
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
            \/ /\ n \in marked
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
       /\ pc' = "Run"
    \/ /\ pc = "Run"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

Spec == Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

\* ----------------------------------------------------------------------
\* Reachability definitions
\* ----------------------------------------------------------------------
RECURSIVE ReachFrom(_)
ReachFrom(S) ==
    IF S = {} THEN {}
    ELSE UNION { {n} \cup ReachFrom(Succ[n]) : n \in S }

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    frontier = {} => marked = ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

\* ----------------------------------------------------------------------
\* Specification and checking
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []Inv1
THEOREM Spec => []Inv2
THEOREM Spec => []Inv3
THEOREM Spec => []PartialCorrectness
THEOREM Spec => Termination

====