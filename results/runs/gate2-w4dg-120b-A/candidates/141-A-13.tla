---- MODULE Reachable ----
\* Misra's variant of breadth-first search: the visited (marked) set and the
\* frontier set may overlap, which is what makes the algorithm amenable to
\* parallel implementation. The spec is written in PlusCal with the attached
\* translation below.
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

\* The single main action with two cases: if the chosen node is unmarked, mark
\* it and add its successors to the frontier (without removing it); if it is
\* already marked, remove it from the frontier. Weak fairness of this action
\* drives termination for finite reachable sets.
Explore ==
  \E v \in frontier :
    /\ IF v \notin marked
       THEN /\ marked' = marked \cup {v}
            /\ frontier' = frontier \cup Succ[v]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {v}
    /\ pc' = IF frontier = {Root} /\ v \notin marked THEN "running" ELSE pc

Next == Explore

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

\* Safety: whatever the frontier holds, every successor of a marked node is
\* either already marked or still waiting in the frontier.
Inv1 == \A v \in marked : Succ[v] \subseteq (marked \cup frontier)

\* Reachable from S: the set of nodes reachable from any node in S via the
\* graph's transitive closure.
ReachableFrom(S) ==
  LET step[X \in SUBSET Nodes] ==
    X \cup {w \in Nodes : \E u \in X : w \in Succ[u]}
  IN  CHOOSE R \in SUBSET Nodes :
        /\ \/ \E n \in Nat : R = step^[n](S)
        /\ \A Y \in SUBSET Nodes :
             (/\ \/ \E n \in Nat : Y = step^[n](S)
              /\ Y \subseteq R) => R \subseteq Y

\* Safety: the marked set and the nodes reachable from the frontier together
\* reach exactly the nodes reachable from themselves together.
Inv2 ==
  (marked \cup frontier) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

\* Safety: the nodes reachable from the root are exactly the marked nodes
\* plus whatever is still reachable from the frontier.
Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness ==
  pc = "done" => marked = ReachableFrom({Root})

Termination == \A n \in Nat : Seq[n] = "done"

====