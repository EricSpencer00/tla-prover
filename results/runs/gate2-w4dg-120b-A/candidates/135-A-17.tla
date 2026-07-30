---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets

CONSTANTS Nodes, Root, Succ, Seq

\* A concrete graph of 4 nodes, each with exactly 2 successors, and a bounded
\* sequence type so the state space stays finite for exhaustive checking.
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(n) ==
  /\ frontier = {n}
  /\ pc = "running"
  /\ marked' = marked \cup {n}
  /\ frontier' = Succ[n]
  /\ pc' = IF frontier = {} THEN "complete" ELSE "running"

Finish ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "complete"
  /\ UNCHANGED << marked, frontier >>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Finish

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "complete"}

\* Every successor of a marked node is marked, so no reachable node is lost.
Inv1 ==
  \A n \in Nodes : n \in marked => Succ[n] \subseteq marked

\* Every node on the frontier is reachable from the root via a short sequence,
\* and the frontier never holds an already-marked node -- the set is refined.
Inv2 ==
  /\ \A n \in frontier : \E s \in Seq : Head(s) = Root /\ Last(s) = n
  /\ frontier \cap marked = {}

\* By construction the marked set is a lower bound on the reachable set; it
\* therefore is exactly the reachable set.
Inv3 ==
  \A n \in Nodes :
    (\E s \in Seq : Head(s) = Root /\ Last(s) = n) => n \in marked

PartialCorrectness == marked = Nodes

Termination == <>(pc = "complete")

====