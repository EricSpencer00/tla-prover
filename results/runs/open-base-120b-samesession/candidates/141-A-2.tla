---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Operators substituted by the .cfg
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Relation representing the graph edges
\* ----------------------------------------------------------------------
Rel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

\* ----------------------------------------------------------------------
\* Reachability operator (reflexive transitive closure)
\* ----------------------------------------------------------------------
ReachFrom(S) == { n \in Nodes :
                    \E m \in S : <<m, n>> \in Rel^* }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Main actions
\* ----------------------------------------------------------------------
AddAndExpand(n) ==
    /\ n \in frontier
    /\ n \notin marked
    /\ marked' = marked \cup {n}
    /\ frontier' = frontier \cup ConnectedToSomeButNotAll(n)
    /\ UNCHANGED pc

RemoveFromFrontier(n) ==
    /\ n \in frontier
    /\ n \in marked
    /\ frontier' = frontier \ {n}
    /\ UNCHANGED <<marked, pc>>

Terminate ==
    /\ frontier = {}
    /\ pc = "run"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next ==
    \/ \E n \in frontier : AddAndExpand(n)
    \/ \E n \in frontier : RemoveFromFrontier(n)
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A m \in marked :
        ConnectedToSomeButNotAll(m) \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    pc = "done" => marked = ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")

==============================================================================