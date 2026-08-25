---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper operators
\* ----------------------------------------------------------------------
RECURSIVE Reach(_)
Reach(S) ==
    IF S = {} THEN {}
    ELSE S \cup Reach( UNION { Succ[n] : n \in S } )

\* Operator that the .cfg substitutes for Succ
ConnectedToSomeButNotAll == [n \in Nodes |-> {}]  \* placeholder; overridden by the configuration

\* Finite version of Seq (simply reuses the standard definition)
LimitedSeq(S) == Seq(S)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

Step ==
    /\ pc = "Run"
    /\ frontier # {}
    /\ \E n \in frontier :
        IF n \notin marked THEN
            /\ marked'   = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
        ELSE
            /\ marked'   = marked
            /\ frontier' = frontier \ {n}
        /\ pc' = IF frontier' = {} THEN "Done" ELSE "Run"

Terminate ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next ==
    \/ Step
    \/ Terminate

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (pc = "Done") => (marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

====