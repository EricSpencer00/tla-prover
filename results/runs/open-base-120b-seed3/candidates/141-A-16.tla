---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS  Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Assumptions about the constants
\* ----------------------------------------------------------------------
ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

Reach(S) == 
    S \cup { y \in Nodes : 
               \E x \in S : <<x, y>> \in TC(SuccRel) }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"

\* ----------------------------------------------------------------------
\* Main action (nondeterministic choice of a node from frontier)
\* ----------------------------------------------------------------------
PickNode ==
    \E n \in frontier :
        \/ /\ n \\notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc' = pc
        \/ /\ n \in marked
           /\ marked' = marked
           /\ frontier' = frontier \ {n}
           /\ pc' = pc

\* ----------------------------------------------------------------------
\* Termination action
\* ----------------------------------------------------------------------
Terminate ==
    /\ frontier = {}
    /\ pc = "run"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Stuttering when already done
\* ----------------------------------------------------------------------
DoneStutter ==
    /\ pc = "done"
    /\ UNCHANGED vars

Next == PickNode \/ Terminate \/ DoneStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "done"
    /\ marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property (termination)
\* ----------------------------------------------------------------------
Termination == []<>(pc = "done")

\* ----------------------------------------------------------------------
\* Operators required by the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq ==
    { s \in Seq : Len(s) <= 5 }

=============================================================================