---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* Operator used in place of the constant Succ (the .cfg substitutes Succ with this)
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Seq (the .cfg substitutes Seq with this)
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Reachability operator (transitive closure using the successor function)
\* ----------------------------------------------------------------------
RECURSIVE Reach(_)
Reach(S) ==
    IF S = {} THEN {}
    ELSE S \cup Reach({ m \in Nodes : \E n \in S : m \in ConnectedToSomeButNotAll(n) })

\* ----------------------------------------------------------------------
\* Main step of Misra's algorithm
\* ----------------------------------------------------------------------
Next ==
    \/ /\ pc = "run"
       /\ frontier \neq {}
       /\ \E n \in frontier :
            /\ n \notin marked
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
            /\ pc'       = "run"
    \/ /\ pc = "run"
       /\ frontier \neq {}
       /\ \E n \in frontier :
            /\ n \in marked
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
            /\ pc'       = IF frontier' = {} THEN "done" ELSE "run"
    \/ /\ pc = "done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>
Spec ==
    Init /\
    [][Next]_vars /\
    WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants required by the .cfg file
\* ----------------------------------------------------------------------
Inv1 ==
    \A n \in marked : ConnectedToSomeButNotAll(n) \subseteq marked \/ frontier

Inv2 ==
    (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (frontier = {} => marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

====