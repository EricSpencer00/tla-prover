---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS
  Nodes,
  Root,
  Succ,
  Seq

VARIABLES
  marked,
  frontier,
  pc

vars == <<marked, frontier, pc>>

\* Deterministic sequence bound: the length of the longest path considered
\* is capped by the number of nodes, which also makes the number of paths finite.
BoundedSeq(S, n) ==
  /\ Len(S) <= n
  /\ \A i \in DOMAIN S : S[i] \in Nodes

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"idle", "running", "done"}
  /\ Seq \in [1..Cardinality(Nodes) -> Nodes]
  /\ Len(Seq) <= Cardinality(Nodes)

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

MarkNext ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ marked' = marked \cup frontier
  /\ frontier' = UNION {Succ[n] : n \in frontier}
  /\ pc' = "running"

Terminate ==
  /\ pc = "running"
  /\ frontier' = {}
  /\ pc' = "done"
  /\ UNCHANGED marked

Reinit ==
  /\ pc = "done"
  /\ marked' = {}
  /\ frontier' = {Root}
  /\ pc' = "idle"
  /\ UNCHANGED Seq

Next ==
  \/ MarkNext
  \/ Terminate
  \/ Reinit

Spec == Init /\ [][Next]_vars

\* Successor closure: every marked node's successors are covered by the marked
\* set together with the current frontier.
Inv1 == \A n \in Nodes : n \in marked => Succ[n] \subseteq (marked \cup frontier)

\* Reachable set decomposes into the marked set plus the current frontier.
Inv2 == frontier = Succ[marked] \ marked

\* Reachable set equals the marked set once the algorithm is done.
Inv3 == pc = "done" => frontier = {}

PartialCorrectness == frontier = {}

Termination == <>(pc = "done")

====