---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC

\*-----------------------------------------------------------------
\* Constants
\*-----------------------------------------------------------------
CONSTANTS
    Nodes,      \* The set of all graph nodes
    Root,       \* The distinguished start node
    Succ        \* A total function Nodes -> SUBSET Nodes giving successors

\*-----------------------------------------------------------------
\* Operator that will be substituted for Succ in the configuration
\*-----------------------------------------------------------------
ConnectedToSomeButNotAll(n) == Succ[n]

\*-----------------------------------------------------------------
\* A finite version of Seq used when the cfg replaces Seq with LimitedSeq
\*-----------------------------------------------------------------
\* Maximum length for the finite sequences (chosen arbitrarily)
MaxSeqLen == 3
LimitedSeq(S) == { s \in Seq(S) : Len(s) <= MaxSeqLen }

\*-----------------------------------------------------------------
\* State variables
\*-----------------------------------------------------------------
VARIABLES
    marked,    \* Set of nodes that have been marked (visited)
    frontier,  \* Set of nodes still to be explored (may overlap with marked)
    pc         \* Program counter: "Run" or "Done"

\*-----------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------
\* Relation representing the edge set of the graph
SuccRel == { <<a, b>> : a \in Nodes /\ b \in Succ[a] }

\* Reachability from a set of nodes (including the nodes themselves)
Reach(S) == S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(SuccRel) }

\*-----------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Run"
    /\ Root \in Nodes

\*-----------------------------------------------------------------
\* The main step of the algorithm
\*-----------------------------------------------------------------
Step ==
    /\ pc = "Run"
    /\ \E n \in frontier :
        \/ /\ n \notin marked
           /\ marked' = marked \cup {n}
           /\ frontier' = frontier \cup Succ[n]
        \/ /\ n \in marked
           /\ marked' = marked
           /\ frontier' = frontier \ {n}
    /\ pc' = IF frontier' = {} THEN "Done" ELSE "Run"

\* Stuttering when the algorithm has terminated
Stutter ==
    /\ pc = "Done"
    /\ UNCHANGED <<marked, frontier, pc>>

Next == Step \/ Stutter

\*-----------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------
Spec == Init /\ [][Next]_<<marked, frontier, pc>>

\*-----------------------------------------------------------------
\* Invariants
\*-----------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Run", "Done"}

Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

Inv2 ==
    (marked \cup Reach(frontier)) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    (pc = "Done") => marked = Reach({Root})

\*-----------------------------------------------------------------
\* Liveness property
\*-----------------------------------------------------------------
Termination == <> (pc = "Done")

\*-----------------------------------------------------------------
\* The constants that must be supplied in the .cfg file
\*-----------------------------------------------------------------
\* (No additional definitions needed; the .cfg will provide Nodes, Root,
\*  Succ, and may replace Succ with ConnectedToSomeButNotAll.)

====