---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "running"

Explore(n) ==
  \/ /\ n \notin marked
     /\ marked' = marked \cup {n}
     /\ frontier' = frontier \cup Succ[n]
     /\ pc' = pc
  \/ /\ n \in marked
     /\ marked' = marked
     /\ frontier' = frontier \ {n}
     /\ pc' = pc

Next == \E n \in frontier: Explore(n)

Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A n \in marked: Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  (marked \cup frontier) = {Root} \cup (UNION {Succ[n] : n \in frontier})

Inv3 ==
  {Root} \cup (UNION {Succ[n] : n \in marked}) =
    marked \cup (UNION {Succ[n] : n \in frontier})

PartialCorrectness ==
  pc = "done" => marked = {Root} \cup (UNION {Succ[n] : n \in frontier})

Termination == pc = "done"

LimitedSeq == SELECT x \in Seq(Nodes) : TRUE

====