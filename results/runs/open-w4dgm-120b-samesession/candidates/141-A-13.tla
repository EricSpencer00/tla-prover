---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

\* Misra's algorithm: marked (visited) set and frontier may overlap, so it
\* stays parallelizable. Termination only guaranteed when the reachable set is finite.
VARIABLES marked, frontier, pc

Init == /\ marked = {}
        /\ frontier = {Root}
        /\ pc = "active"

\* One action with two cases, nondeterministically chosen from the frontier.
Explore(n) == /\ n \in frontier
              /\ IF n \notin marked
                 THEN /\ marked' = marked \cup {n}
                      /\ frontier' = frontier \cup Succ[n]
                 ELSE /\ marked' = marked
                      /\ frontier' = frontier \ {n}
              /\ pc' = IF frontier' = {} THEN "done" ELSE "active"

Next == \E n \in Nodes : Explore(n)

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

TypeOK == /\ marked \subseteq Nodes
          /\ frontier \subseteq Nodes
          /\ pc \in {"active", "done"}

\* Every successor of a marked node is already marked or still waiting in the frontier.
Inv1 == \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* Frontier nodes are exactly those that must still be explored to reach
\* everything reachable from the visited-plus-frontier frontier.
Inv2 == (marked \cup frontier) = (marked \cup (UNION {Succ[n] : n \in frontier}))

\* Reachable is partitioned into finished (marked) and still-frontier nodes.
Inv3 == (UNION {Succ[n] : n \in {Root} \cup marked \cup frontier})
          = (UNION {Succ[n] : n \in marked}) \cup (UNION {Succ[n] : n \in frontier})

PartialCorrectness == (pc = "done") => (UNION {Succ[n] : n \in marked}) = (UNION {Succ[n] : n \in Nodes})

FiniteWeakFairness == \A n \in Nodes : WF_vars(Explore(n))

Termination == \A n \in Nodes : Explore(n) ~> (frontier = {})

====