---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

ReachSet(S) == { y \in Nodes : \E x \in S : <<x, y>> \in TC(SuccRel) }

\* Operator used by the .cfg substitution for Succ
ConnectedToSomeButNotAll(n) == Succ[n]

\* Finite version of Seq (used by the .cfg substitution for Seq)
LimitedSeq == Seq(Nodes)

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

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
Next ==
    \/ /\ pc = "Run"
       /\ \E n \in frontier :
            /\ IF n \\notin marked THEN
                  /\ marked' = marked \cup {n}
                  /\ frontier' = frontier \cup Succ[n]
               ELSE
                  /\ marked' = marked
                  /\ frontier' = frontier \ {n}
            /\ UNCHANGED pc
    \/ /\ pc = "Run"
       /\ frontier = {}
       /\ pc' = "Done"
       /\ UNCHANGED <<marked, frontier>>
    \/ /\ pc = "Done"
       /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>> /\ WF_<<marked, frontier, pc>>(Next)

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
    marked \cup ReachSet(frontier) = ReachSet(marked \cup frontier)

Inv3 ==
    ReachSet({Root}) = marked \cup ReachSet(frontier)

PartialCorrectness ==
    /\ pc = "Done"
    /\ marked = ReachSet({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

====