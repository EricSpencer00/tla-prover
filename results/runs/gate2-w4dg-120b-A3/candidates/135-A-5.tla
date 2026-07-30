---- MODULE MCReachable ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Done == "done"
Work == "work"

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {Work, Done}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = Work

Mark(n) ==
  /\ n \in frontier
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ UNCHANGED pc

Finish ==
  /\ frontier = {}
  /\ pc' = Done
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Mark(n)
  \/ Finish

Spec == Init /\ [][Next]_vars

Inv1 == frontier \subseteq Succ[Root]
Inv2 == marked \subseteq Union({Succ[n] : n \in Nodes})
Inv3 == marked = Nodes
PartialCorrectness == \A n \in Nodes : FrontierHolds(n)

FrontierHolds(n) ==
  \/ n \in frontier
  \/ \E p \in LimitedSeq(Nodes) :
       /\ Len(p) >= 1
       /\ p[1] = Root
       /\ p[Len(p)] = n
       /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]

Termination == <>(pc = Done)

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == {s \in Seq(S) : Len(s) <= Cardinality(Nodes)}

====