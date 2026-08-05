---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ frontier \cap marked = {}
  /\ pc \in {"init", "explore", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "explore"

ExploreStep(n) ==
  /\ pc = "explore"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ pc' = "explore"

Done ==
  /\ pc = "explore"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == \E n \in Nodes : ExploreStep(n) \/ Done

Spec == Init /\ [][Next]_vars

Inv1 ==
  frontier \subseteq Nodes \ marked

Inv2 ==
  marked \subseteq Reachable

Inv3 ==
  Reachable = marked

PartialCorrectness ==
  \A t \in Reachable : \E i \in 1..Len(S) : S[i] = t

Reachable ==
  {n \in Nodes : \E seq \in LimitedSeq(Nodes) : seq[1] = Root /\ seq[Len(seq)] = n /\ \A j \in 1..(Len(seq) - 1) : seq[j + 1] \in Succ[seq[j]]}

Termination == <>(pc = "done")

====