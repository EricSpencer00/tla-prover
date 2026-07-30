---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

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

Explore ==
  /\ frontier # {}
  /\ pc = "running"
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
          /\ marked' = marked
  /\ pc' = "running"

Terminate ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup (ReachableFromSet(Nodes, frontier)) =
    ReachableFromSet(Nodes, marked \cup frontier)

Inv3 ==
  ReachableFromSet(Nodes, {Root}) = marked \cup ReachableFromSet(Nodes, frontier)

PartialCorrectness ==
  (pc = "done") => (marked = ReachableFromSet(Nodes, {Root}))

Termination == (Cardinality(ReachableFromSet(Nodes, {Root})) < \infinity) ~> (pc = "done")

ConnectedToSomeButNotAll == {n \in Nodes : Cardinality(Succ[n]) > 0}

LimitedSeq == {s \in Seq(Nodes) : Cardinality(SUBSET s) = Len(s)}

====