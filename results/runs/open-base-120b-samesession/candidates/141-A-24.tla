---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Nodes,          \* The set of all graph nodes
    Root,           \* The distinguished start node
    Succ            \* A total function Nodes -> SUBSET Nodes giving successors

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Relation version of the successor function
SuccRel == { <<n, m>> : n \in Nodes /\ m \in Succ[n] }

\* Nodes reachable (by a finite non‑empty path) from a set S using Succ
REACHABLE(S) ==
    LET
        TC == TC(SuccRel)               \* transitive closure of SuccRel
    IN
        S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State predicates
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"

\* Main step: pick a node from the frontier nondeterministically
Next ==
    \E n \in frontier :
        /\ IF n \\notin marked
           THEN /\ marked' = marked \cup {n}
                /\ frontier' = frontier \cup Succ[n]
                /\ pc' = pc
           ELSE /\ marked' = marked
                /\ frontier' = frontier \ {n}
                /\ pc' = pc

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
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    marked \cup REACHABLE(frontier) = REACHABLE(marked \cup frontier)

Inv3 ==
    REACHABLE({Root}) = marked \cup REACHABLE(frontier)

PartialCorrectness ==
    (frontier = {}) => marked = REACHABLE({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (frontier = {})

\* ----------------------------------------------------------------------
\* Operators required by the .cfg file
\* ----------------------------------------------------------------------
\* A (possibly bounded) version of the successor function used by the
\* configuration file in place of Succ.
ConnectedToSomeButNotAll(n) == Succ[n]

\* A finite version of Seq for model checking (the bound 5 is arbitrary)
LimitedSeq(E) == { s \in Seq(E) : Len(s) <= 5 }

==============================================================================