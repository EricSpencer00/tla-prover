---- MODULE Reachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

\* A hierarchy of sets: nodes reachable from the marked set, and from the
\* frontier. Frontier is allowed to intersect marked, which is what Misra's
\* variant does differently from ordinary BFS.
ReachableFrom(S) == UNION { Succ[n] : n \in S }

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "start"

\* The only action, with its two nondeterministic cases. Adding successors
\* to the frontier never removes the node itself, so marked and frontier may
\* overlap.
Step(n) ==
  /\ n \in frontier
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ frontier' = frontier \ {n}
            /\ marked' = marked
  /\ UNCHANGED pc

Next ==
  \E n \in Nodes : Step(n)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"start", "done"}

\* Every successor of a marked node is either already marked or still to be explored.
Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

\* The reachable nodes from the explored plus frontier cover exactly the
\* reachable nodes from the union of explored and frontier.
Inv2 ==
  ReachableFrom(marked \cup frontier) = ReachableFrom(marked) \cup ReachableFrom(frontier)

\* Reachable from the root is exactly the explored set plus what's reachable from the frontier.
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  \A n \in Nodes : (n \in marked) <=> (n \in ReachableFrom({Root}))

Termination == (pc = "start") ~> (pc = "done")

====