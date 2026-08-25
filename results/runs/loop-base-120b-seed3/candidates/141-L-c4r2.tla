---- MODULE Reachable ----
EXTENDS Naturals, Sequences, TLC, Temporal

CONSTANTS
    Nodes,            \* The set of all graph nodes
    Root,             \* The distinguished start node
    Succ              \* Successor function: [Nodes -> SUBSET Nodes]

\* ----------------------------------------------------------------------
\* Operator that the .cfg will substitute for Succ
\* (Usually a finite/bounded version of Succ)
ConnectedToSomeButNotAll(n) ==
    IF n \in Nodes THEN {} ELSE {}

\* ----------------------------------------------------------------------
\* Finite version of Seq used by the .cfg
LimitedSeq(S) ==
    { s \in Seq(S) : Len(s) <= 5 }

\* ----------------------------------------------------------------------
\* Variables
VARIABLES
    marked,    \* Set of visited (marked) nodes
    frontier,  \* Set of frontier nodes (may overlap with marked)
    pc         \* Program counter: "run" or "done"

\* ----------------------------------------------------------------------
\* Helper: relation induced by Succ
SuccRel == { <<x, y>> : x \in Nodes /\ y \in Succ[x] }

\* Reachable nodes from a set of sources (including the sources themselves)
Reach(S) ==
    S \cup { y \in Nodes : \E x \in S : <<x, y>> \in TC(SuccRel) }

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "run"
    /\ Root \in Nodes

\* ----------------------------------------------------------------------
\* Main action: pick a node from the frontier
PickNode ==
    \E n \in frontier :
        /\ IF n \notin marked
              THEN /\ marked' = marked \cup {n}
                   /\ frontier' = frontier \cup Succ[n]
              ELSE /\ marked' = marked
                   /\ frontier' = frontier \ {n}
        /\ pc' = pc

\* ----------------------------------------------------------------------
\* Termination action
Terminate ==
    /\ pc = "run"
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

\* ----------------------------------------------------------------------
\* Stuttering when done
StutterDone ==
    /\ pc = "done"
    /\ UNCHANGED <<marked, frontier, pc>>

\* ----------------------------------------------------------------------
Next ==
    \/ (pc = "run" /\ frontier # {} /\ PickNode)
    \/ Terminate
    \/ StutterDone

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    Init /\ []_(<<marked, frontier, pc>>)(Next) /\ WF_(<<marked, frontier, pc>>)(Next)

\* ----------------------------------------------------------------------
\* Invariants
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"run", "done"}

Inv1 ==
    \A m \in marked : Succ[m] \subseteq marked \cup frontier

Inv2 ==
    marked \cup Reach(frontier) = Reach(marked \cup frontier)

Inv3 ==
    Reach({Root}) = marked \cup Reach(frontier)

PartialCorrectness ==
    /\ pc = "done"
    /\ marked = Reach({Root})

\* ----------------------------------------------------------------------
\* Liveness property: termination
Termination == <> (pc = "done")
====