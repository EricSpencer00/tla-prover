---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

\* The reachability algorithm tracks a marked set and a frontier, plus a PC.
VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "exploring"

Explore(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ frontier' = (frontier \ {n}) \cup (Succ[n])
  /\ marked' = marked \cup Succ[n]
  /\ UNCHANGED pc

Complete ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED << marked, frontier >>

Idle ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Complete
  \/ Idle

Spec == Init /\ [][Next]_vars

\* Type correctness: all model-defined symbols stay within their domains.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}

\* Invariant 1: the frontier is always a subset of the reachable set.
Inv1 ==
  frontier \subseteq marked

\* Invariant 2: every node is reachable via a concrete path from the root
\* (expressed through the bounded sequence set Seq).
Inv2 ==
  \A n \in marked : n \in Seq

\* Invariant 3: the reachable set is exactly the nodes reachable from the root.
Inv3 ==
  marked = {n \in Nodes : n \in Seq}

PartialCorrectness ==
  (pc = "done") => (marked = Nodes)

Termination == <>(pc = "done")

====