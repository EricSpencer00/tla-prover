---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Operators required by the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == Seq(S) \* Finite sequences (Seq is already finite in TLA+)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SuccRel == { <<n,m>> : n \in Nodes /\ m \in Succ[n] }

Reach(S) == TC(SuccRel, S)  \* nodes reachable from a set S via Succ

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
PickNode ==
    /\ frontier # {}
    /\ \E n \in frontier :
          /\ IF n \notin marked
                THEN /\ marked'   = marked \cup {n}
                     /\ frontier' = frontier \cup Succ[n]
                ELSE /\ marked'   = marked
                     /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "Done" ELSE "Run"

TerminateStutter ==
    /\ frontier = {}
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == PickNode \/ TerminateStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (frontier = {} /\ pc = "Done") => marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {} /\ pc = "Done")
====