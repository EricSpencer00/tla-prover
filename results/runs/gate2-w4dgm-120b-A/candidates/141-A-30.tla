---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

NodeReachable(n) == \E m \in Nodes : m \in frontier /\ n \in Succ[m]

Nxt == CHOOSE n \in frontier : TRUE

ExploreUnmarked ==
  /\ pc = "running"
  /\ frontier # {}
  /\ Nxt \notin marked
  /\ marked' = marked \cup {Nxt}
  /\ frontier' = frontier \cup Succ[Nxt]
  /\ pc' = pc

ExploreMarked ==
  /\ pc = "running"
  /\ frontier # {}
  /\ Nxt \in marked
  /\ frontier' = frontier \ {Nxt}
  /\ pc' = pc

Terminate ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next == ExploreUnmarked \/ ExploreMarked \/ Terminate

Spec == Init /\ [][Next]_vars

ReachableFromRoot ==
  {x \in Nodes : \E k \in 1..Cardinality(Nodes) : \E s \in LimitedSeq(Nodes, k) : s[1] = Root /\ \A i \in 1..(k - 1) : x \in Succ[s[i]]}

Inv1 == \A m \in marked : \A n \in Nodes : n \in Succ[m] => (n \in marked \/ n \in frontier)

Inv2 == ReachableFromRoot = (marked \cup frontier) \ (\ReachableFromRoot \cap frontier)

Inv3 == ReachableFromRoot = marked \cup {n \in Nodes : NodeReachable(n)}

PartialCorrectness == ReachableFromRoot = marked

Termination == pc = "terminated"

ConnectedToSomeButNotAll == Nodes

LimitedSeq == FiniteSequences.LimitedSeq

====