---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
RECURSIVE Path(_, _)

Path(x, y) == 
    \/ x = y
    \/ \E z \in Succ[x] : Path(z, y)

ReachableFromNode(n) == { m \in Nodes : Path(n, m) }

ReachableFromSet(S) == UNION { ReachableFromNode(s) : s \in S }

\* ----------------------------------------------------------------------
\* Successor operator (will be overridden by ConnectedToSomeButNotAll via .cfg)
\* ----------------------------------------------------------------------
Succ(n) == ConnectedToSomeButNotAll[n]

\* ----------------------------------------------------------------------
\* Operator substituted for Succ in the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) ==
    (* Abstract definition – concrete value supplied by the model checker *)
    {} 

\* ----------------------------------------------------------------------
\* Limited version of Seq (replaces Seq from Sequences)
\* ----------------------------------------------------------------------
CONSTANT MaxSeqLen
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

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
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

\* ----------------------------------------------------------------------
\* Main action
\* ----------------------------------------------------------------------
ChooseNode == 
    \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
           /\ pc' = pc
        \/ /\ n \in marked
           /\ marked' = marked
           /\ frontier' = frontier \ {n}
           /\ pc' = pc

Terminate == 
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = "Done"

Next == 
    \/ /\ frontier # {}
       /\ ChooseNode
    \/ Terminate

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<marked, frontier, pc>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 == (marked \cup ReachableFromSet(frontier)) = ReachableFromSet(marked \cup frontier)

Inv3 == ReachableFromNode(Root) = marked \cup ReachableFromSet(frontier)

PartialCorrectness == (frontier = {}) => (marked = ReachableFromNode(Root))

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == []<>(frontier = {})

=============================================================================