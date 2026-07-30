---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The two cases of the main action are chosen nondeterministically from
\* the frontier.  They keep the visited and frontier sets overlapping.
Explore(n) ==
  /\ n \in frontier
  /\ marked' = IF n \notin marked THEN marked \cup {n} ELSE marked
  /\ frontier' = IF n \notin marked THEN frontier \cup Succ[n] ELSE frontier \ {n}
  /\ pc' = IF frontier = {n} \cup (IF n \notin marked THEN Succ[n] ELSE {}) /\ frontier = {n} THEN "done" ELSE pc

Next ==
  \E n \in Nodes: Explore(n)

Spec == Init /\ [][Next]_vars
        /\ WF_vars(Next)

\* Every successor of a marked node is either marked already or in the
\* frontier: no reachable node is dropped past the two overlapping sets.
Inv1 ==
  \A n \in marked: Succ[n] \subseteq (marked \cup frontier)

\* The reachable nodes from the visited-or-frontier set are the reachable
\* nodes from the visited set plus the reachable nodes from the frontier.
Inv2 ==
  Reachable(marked \cup frontier) = Reachable(marked) \cup Reachable(frontier)

\* Reachable from the root is exactly the visited set plus the reachable
\* nodes from the frontier (a restatement of Inv2 for the root).
Inv3 ==
  Reachable({Root}) = marked \cup Reachable(frontier)

PartialCorrectness ==
  (pc = "done") => (marked = Reachable({Root}))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

Termination ==
  Cardinality(Reachable({Root})) < Cardinality(Nodes) => <>(pc = "done")

====