---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* A finite version of the sequence operator for model checking.
CONSTANT MaxSeqLen == 5
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* Operator that will be substituted for Succ in the .cfg file.
ConnectedToSomeButNotAll(n) == Succ[n] \ { n }

\* ----------------------------------------------------------------------
\* Reachability definitions
\* ----------------------------------------------------------------------
RECURSIVE Paths(_,_)
Paths(0, S) == S
Paths(k+1, S) == UNION { Succ[n] : n \in Paths(k, S) }

Reach(S) == UNION { Paths(k, S) : k \in Nat }

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

\* ----------------------------------------------------------------------
\* Invariants described in the specification
\* ----------------------------------------------------------------------
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 == Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness == 
    /\ frontier = {}
    /\ marked = Reach({Root})

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
Explore ==
    \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup Succ[n]
        /\ pc' = pc

Remove ==
    \E n \in frontier :
        /\ n \in marked
        /\ marked' = marked
        /\ frontier' = frontier \ {n}
        /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc = "run"
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Stutter ==
    /\ pc = "done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == Explore \/ Remove \/ Terminate \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == []<>(frontier = {})

=============================================================================