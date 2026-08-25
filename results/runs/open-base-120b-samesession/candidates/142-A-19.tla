---- MODULE ReachableProofs ----
EXTENDS SeqReachAlg, ReachProofs

CONSTANTS Nodes, Root

VARIABLES Marked, Frontier, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeInv ==
    /\ Marked \subseteq Nodes
    /\ Frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is either marked or in the frontier
\* ----------------------------------------------------------------------
Inv1 ==
    /\ TypeInv
    /\ \A n \in Marked :
         \A s \in Succ[n] :
            s \in Marked \/ s \in Frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ ReachFrom(Frontier) = ReachFrom(marked ∪ frontier)
\* ----------------------------------------------------------------------
Inv2 ==
    Marked \cup ReachFrom(Frontier) = ReachFrom(Marked \cup Frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: ReachFrom({Root}) = marked ∪ ReachFrom(Frontier)
\* ----------------------------------------------------------------------
Inv3 ==
    ReachFrom({Root}) = Marked \cup ReachFrom(Frontier)

\* ----------------------------------------------------------------------
\* Set of invariants for the model checker
\* ----------------------------------------------------------------------
INVARIANTS == { Inv1, Inv2, Inv3 }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Marked = {}
    /\ Frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Algorithm actions (abstracted)
\* ----------------------------------------------------------------------
AddFrontier ==
    /\ pc = "run"
    /\ \E n \in Marked :
         \E s \in Succ[n] :
            /\ s \notin Marked
            /\ s \notin Frontier
            /\ Frontier' = Frontier \cup {s}
            /\ UNCHANGED <<Marked, pc>>

MarkNode ==
    /\ pc = "run"
    /\ \E n \in Frontier :
         /\ n \notin Marked
         /\ Marked' = Marked \cup {n}
         /\ Frontier' = Frontier \setminus {n}
         /\ UNCHANGED pc

Done ==
    /\ pc = "run"
    /\ Frontier = {}
    /\ Marked = ReachFrom({Root})
    /\ pc' = "done"
    /\ UNCHANGED <<Marked, Frontier>>

Next ==
    AddFrontier \/ MarkNode \/ Done

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Marked, Frontier, pc>>

\* ----------------------------------------------------------------------
\* Property expressing partial correctness upon termination
\* ----------------------------------------------------------------------
TerminationCorrectness ==
    (pc = "done") => (Marked = ReachFrom({Root}))

PROPERTIES == { TerminationCorrectness }

====