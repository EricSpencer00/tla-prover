---- MODULE Reachable ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANTS
    Nodes,          \* The set of all graph nodes
    Root,           \* The distinguished start node (Root \\in Nodes)
    Succ            \* Successor function: [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Operators overridden by the .cfg file
\* ----------------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\* ----------------------------------------------------------------------
\* Finite version of Seq (used by the .cfg file)
\* ----------------------------------------------------------------------
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= 5 }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* Auxiliary definitions
\* ----------------------------------------------------------------------
\* Relation representing the graph edges
\*   We construct the relation as a union of singleton sets containing
\*   the ordered pairs <<x, y>> for each edge (x,y).
SuccRel ==
    UNION {
        { <<x, y>> } :
            /\ x \in Nodes
            /\ y \in Succ[x]
    }

\* Nodes reachable from a set of start nodes (including the starts)
ReachFrom(S) ==
    { n \in Nodes :
        \E s \in S : <<s, n>> \in TC(SuccRel) }

\* ----------------------------------------------------------------------
\* Initialisation
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ /\ frontier # {}
       /\ \E n \in frontier :
            \/ /\ n \notin marked
               /\ marked'   = marked \cup {n}
               /\ frontier' = frontier \cup Succ[n]
               /\ pc'       = "run"
            \/ /\ n \in marked
               /\ marked'   = marked
               /\ frontier' = frontier \ {n}
               /\ pc'       = "run"
    \/ /\ frontier = {}
       /\ pc = "run"
       /\ pc' = "done"
       /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup ReachFrom(frontier)) = ReachFrom(marked \cup frontier)

Inv3 ==
    ReachFrom({Root}) = marked \cup ReachFrom(frontier)

PartialCorrectness ==
    /\ pc = "done"
    /\ marked = ReachFrom({Root})

\* ----------------------------------------------------------------------
\* Liveness property
\* ----------------------------------------------------------------------
Termination == <> (pc = "done")
====