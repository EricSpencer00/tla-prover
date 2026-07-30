---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore ==
  /\ frontier # {}
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
  /\ pc' = "terminated"
  /\ UNCHANGED <<marked, frontier>>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars /\ WF_vars(Explore)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "terminated"}

Inv1 ==
  \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) \cup ReachableFrom(frontier) = ReachableFrom(marked \cup frontier)

Inv3 ==
  ReachableFrom({Root}) = marked \cup ReachableFrom(frontier)

PartialCorrectness == IF frontier = {} THEN marked = ReachableFrom({Root}) ELSE TRUE

Termination == (\A n \in frontier : n \in Nodes) ~> (frontier = {})

ConnectedToSomeButNotAll ==
  \E x \in Nodes : Succ[x] = ReachableFrom({y \in Nodes : y # x})

LimitedSeq ==
  Seq == (\A n \in Nat : TRUE)
====