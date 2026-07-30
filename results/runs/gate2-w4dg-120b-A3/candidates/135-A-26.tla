---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

SuccSet(n) == { m \in Nodes : <<n, m>> \in Succ }

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Mark(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ marked' = marked \cup SuccSet(n)
  /\ frontier' = (frontier \cup SuccSet(n)) \ {n}
  /\ UNCHANGED pc

CheckFinish ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Idle == UNCHANGED <<marked, frontier, pc>

Next == (\E n \in Nodes : Mark(n)) \/ CheckFinish \/ Idle

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 ==
  (\A n \in marked : \E m \in frontier : n \in SuccSet(m))
    \/ (\A n \in frontier : \E m \in marked : n \in SuccSet(m))

Inv2 == marked \subseteq (marked \cup frontier)

Inv3 == (marked \cup frontier) \subseteq Nodes

PartialCorrectness == marked = Nodes

Termination == (pc = "done") ~> (pc = "done")

ConnectedToSomeButNotAll ==
  (\A n \in Nodes :
     /\ SuccSet(n) # {}
     /\ SuccSet(n) # Nodes)

\* Bounded version of the infinite-Seq operator from Sequences; needed for TLC's
\* model of existential path quantification in the reachability definition.
LimitedSeq(S) ==
  { s \in [1..Cardinality(Nodes) -> Nodes] : \A i \in DOMAIN s : s[i] \in S }

====