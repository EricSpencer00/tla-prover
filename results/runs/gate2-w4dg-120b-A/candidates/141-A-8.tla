---- MODULE Reachable ----
EXTENDS Naturals

CONSTANTS
    Nodes,
    Root,
    Succ,
    Seq

VARIABLES marked, frontier, pc

TypeOK ==
    /\ marked \subseteq Nodes
    /\ frontier \subseteq Nodes
    /\ pc \in {"running", "done"}

Init ==
    /\ marked = {}
    /\ frontier = {Root}
    /\ pc = "running"

\* Misra's BFS variant: the visited (marked) set and the frontier may overlap,
\* which is what makes it parallelizable.
ExploreStep ==
    /\ frontier # {}
    /\ pc' = "running"
    /\ LET n == CHOOSE x \in frontier : TRUE IN
         IF n \notin marked
         THEN /\ marked' = marked \cup {n}
              /\ frontier' = frontier \cup Succ[n]
         ELSE /\ marked' = marked
              /\ frontier' = frontier \ {n}
    /\ UNCHANGED pc

Terminate ==
    /\ frontier = {}
    /\ pc' = "done"
    /\ UNCHANGED <<marked, frontier>>

Next == ExploreStep \/ Terminate

\* Fairness: the main step cannot keep the frontier alive forever.
Spec ==
    /\ Init
    /\ [][Next]_<<marked, frontier, pc>>
    /\ WF_vars(ExploreStep)

\* The main safety story: every node reachable from the root is either already
\* marked or still reachable via the frontier, and the two sets together cover
\* exactly the reachable nodes.
Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier
Inv2 == Reachable(Root, marked) \cup Reachable(Root, frontier) = Reachable(Root, marked \cup frontier)
Inv3 == Reachable(Root, marked) \cup Reachable(Root, frontier) = Reachable(Root, Nodes)

PartialCorrectness == \A n \in Nodes : n \in marked <=> Reachable(Root, {n})

Termination == pc = "done"

====