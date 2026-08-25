---- MODULE Reachable ----
EXTENDS Sequences, Naturals

CONSTANTS Nodes, Root, Succ

\* ----------------------------------------------------------------------
\* Replacement operators required by the configuration
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll == Succ
LimitedSeq(S) == Seq(S)

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
    /\ pc = "Run"

\* ----------------------------------------------------------------------
\* Edge relation induced by the successor function
\* ----------------------------------------------------------------------
Edge == [x \in Nodes, y \in Nodes |-> y \in ConnectedToSomeButNotAll[x]]

\* ----------------------------------------------------------------------
\* Reachability operator: all nodes reachable (by zero or more edges)
\* from a set of source nodes
\* ----------------------------------------------------------------------
ReachFrom(S) ==
    { y \in Nodes : \E x \in S : <<x, y>> \in TC(Edge) } \cup S

\* ----------------------------------------------------------------------
\* Main algorithm action (nondeterministically picks a node from frontier)
\* ----------------------------------------------------------------------
MainAction ==
    /\ frontier # {}
    /\ \E n \in frontier :
        /\ IF n \notin marked THEN
               /\ marked' = marked \cup {n}
               /\ frontier' = frontier \cup ConnectedToSomeButNotAll[n]
           ELSE
               /\ marked' = marked
               /\ frontier' = frontier \ {n}
        /\ UNCHANGED pc

\* ----------------------------------------------------------------------
\* Stuttering step when the algorithm has terminated
\* ----------------------------------------------------------------------
TerminateStutter ==
    /\ frontier = {}
    /\ UNCHANGED <<marked, frontier, pc>>

Next == MainAction \/ TerminateStutter

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ Root \in Nodes

Inv1 ==
    \A n \in marked :
        ConnectedToSomeButNotAll[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup ReachFrom(frontier) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    (frontier = {}) => (marked = ReachFrom({Root}))

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

====