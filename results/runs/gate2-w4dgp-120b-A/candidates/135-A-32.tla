---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "complete"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

InitStep ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "exploring"
  /\ UNCHANGED <<marked, frontier>>

ExploreStep(n) ==
  /\ pc = "exploring"
  /\ n \in frontier
  /\ \E y \in Succ[n] :
       /\ y \notin marked
       /\ marked' = marked \cup {y}
       /\ frontier' = frontier \cup {y}
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED pc

CompleteStep ==
  /\ pc = "exploring"
  /\ frontier = {}
  /\ pc' = "complete"
  /\ UNCHANGED <<marked, frontier>>

DoneStep ==
  /\ pc = "complete"
  /\ pc' = "idle"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ InitStep
  \/ \E n \in Nodes : ExploreStep(n)
  \/ CompleteStep
  \/ DoneStep

Spec == Init /\ [][Next]_vars

Inv1 == \A u \in marked : \E w \in frontier : u \in Succ[w]
Inv2 == \A u \in marked : u # Root => \E w \in marked : u \in Succ[w]
Inv3 == \A u \in Nodes : \E seq \in LimitedSeq : seq[1] = Root /\ seq[Len(seq)] = u /\ \A i \in 2..Len(seq) : seq[i] \in Succ[seq[i - 1]]
PartialCorrectness == \A u \in marked : u # Root => \E w \in marked : u \in Succ[w]

Termination == <>(pc = "idle")

====