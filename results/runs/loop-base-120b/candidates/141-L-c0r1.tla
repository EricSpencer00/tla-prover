---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Operator that will be substituted for Succ in the .cfg file
\* (a default definition; the .cfg may override it)
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll == [n \in Nodes |-> {}]

\* ----------------------------------------------------------------------
\* A finite version of Seq for model checking
\* ----------------------------------------------------------------------
CONSTANT MaxSeqLen
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\* ----------------------------------------------------------------------
\* State variables
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
\* Edge relation derived from the successor function
\* ----------------------------------------------------------------------
Edge == { <<n, m>> : n \in Nodes /\ m \in ConnectedToSomeButNotAll[n] }

\* ----------------------------------------------------------------------
\* Reachability from a set of nodes using the transitive closure
\* ----------------------------------------------------------------------
Reach(S) == TC(Edge, S)

\* ----------------------------------------------------------------------
\* Main step: pick a node from the frontier and act
\* ----------------------------------------------------------------------
PickAndMark ==
    \E n \in frontier :
        /\ n \notin marked
        /\ marked' = marked \cup {n}
        /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
        /\ pc' = pc

RemoveMarked ==
    \E n \in frontier :
        /\ n \in marked
        /\ marked' = marked
        /\ frontier' = frontier \ {n}
        /\ pc' = pc

Terminate ==
    /\ frontier = {}
    /\ pc = "Run"
    /\ pc' = "Done"
    /\ UNCHANGED <<marked, frontier>>

Next == PickAndMark \/ RemoveMarked \/ Terminate

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
    /\ pc \in {"Run", "Done"}

\* ----------------------------------------------------------------------
\* Invariant 1: every successor of a marked node is in marked or frontier
\* ----------------------------------------------------------------------
Inv1 == \A n \in marked : ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

\* ----------------------------------------------------------------------
\* Invariant 2: marked ∪ Reach(frontier) = Reach(marked ∪ frontier)
\* ----------------------------------------------------------------------
Inv2 == marked \cup Reach(frontier) = Reach(marked \cup frontier)

\* ----------------------------------------------------------------------
\* Invariant 3: Reach({Root}) = marked ∪ Reach(frontier)
\* ----------------------------------------------------------------------
Inv3 == Reach({Root}) = marked \cup Reach(frontier)

\* ----------------------------------------------------------------------
\* Partial correctness: when terminated, marked = reachable from Root
\* ----------------------------------------------------------------------
PartialCorrectness == (pc = "Done") => (marked = Reach({Root}))

\* ----------------------------------------------------------------------
\* Liveness property: eventual termination
\* ----------------------------------------------------------------------
Termination == <> (pc = "Done")

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK /\ Inv1 /\ Inv2 /\ Inv3 /\ PartialCorrectness
PROPERTIES == Termination

====