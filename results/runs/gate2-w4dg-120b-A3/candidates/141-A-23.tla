---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "run"

Step ==
  /\ pc = "run"
  /\ frontier # {}
  /\ \E n \in frontier :
       \/ /\ n \notin marked
          /\ marked' = marked \cup {n}
          /\ frontier' = frontier \cup Succ[n]
       \/ /\ n \in marked
          /\ frontier' = frontier \ {n}
  /\ pc' = "run"

Terminate ==
  /\ frontier = {}
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Done ==
  /\ pc = "run"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Terminate \/ Done

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"run", "done"}

Inv1 ==
  /\ \A n \in marked : Succ[n] \subseteq (marked \cup frontier)

Inv2 ==
  /\ (marked \cup frontier) \cup (ReachableFromSet(Nodes, frontier)) = ReachableFromSet(Nodes, marked \cup frontier)

Inv3 ==
  /\ ReachableFromSet(Nodes, {Root}) = marked \cup ReachableFromSet(Nodes, frontier)

PartialCorrectness ==
  /\ pc = "done"
  /\ marked = ReachableFromSet(Nodes, {Root})

Termination ==
  /\ \A x \in Nodes : \A s \in Seq(Nodes) : TRUE
  /\ WF_vars(Step)
  /\ WF_vars(Done)
====