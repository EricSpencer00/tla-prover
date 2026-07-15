---- MODULE Reachable ----
EXTENDS Naturals, TLC

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

\* ----------------------------------------------------------------------
\* State definitions
\* ----------------------------------------------------------------------
Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "Running"

Running ==
    CHOOSE n \in frontier :
        IF n \notin marked THEN
            /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
            /\ pc' = "Running"
        ELSE
            /\ marked' = marked
            /\ frontier' = frontier \ {n}
            /\ pc' = "Running"

Terminated ==
    /\ frontier = {}
    /\ marked' = marked
    /\ frontier' = frontier
    /\ pc' = "Done"

Next ==
    \/ \E _ \in {1} : Running
    \/ Terminated

Spec ==
    Init /\ [][Next]_<<marked, frontier, pc>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"Running", "Done"}

\* ----------------------------------------------------------------------
\* Safety invariants from the description
\* ----------------------------------------------------------------------
\* Inv1: Every successor of a marked node is in marked or frontier
Inv1 ==
    \A n \in marked : Succ[n] \subseteq marked \cup frontier

\* Inv2: Reachable nodes from the union of marked and frontier equals
\*       the union of marked and reachable nodes from frontier
Inv2 ==
    \A X \in SUBSET Nodes :
        (X = marked \/ X = frontier) =>
            (X \cup \bigcup_{n \in X} Succ[n]) =
            (marked \cup \bigcup_{n \in frontier} Succ[n])

\* Inv3: Reachable from Root equals marked plus reachable from frontier
Inv3 ==
    (marked \cup \bigcup_{n \in frontier} Succ[n]) = ReachableFromRoot

\* Auxiliary definition of reachable set from a given set of nodes
ReachableFrom(S) ==
    LET Rec(Src) ==
        IF Src = {} THEN {}
        ELSE
            LET n == CHOOSE x \in Src : TRUE IN
            Succ[n] \cup Rec(Src \ {n})
    IN Src \cup Rec(Src)

ReachableFromRoot == ReachableFrom({Root})

\* Partial correctness: when terminated, marked equals exactly the reachable set
PartialCorrectness ==
    (pc = "Done") => (marked = ReachableFromRoot)

\* ----------------------------------------------------------------------
\* Liveness property (termination under weak fairness)
\* ----------------------------------------------------------------------
Termination == <>[](pc = "Done")

=============================================================================