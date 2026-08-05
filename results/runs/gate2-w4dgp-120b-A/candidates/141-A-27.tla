---- MODULE Reachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>
Finite == frontier = {}

AssumeRoot == Root \in Nodes

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"scanning", "done"}

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "scanning"

MarkOrRemove(n) ==
  /\ n \in frontier
  /\ IF n \notin marked
       THEN /\ marked' = marked \cup {n}
            /\ frontier' = frontier \cup Succ[n]
       ELSE /\ marked' = marked
            /\ frontier' = frontier \ {n}
  /\ pc' = pc

Terminate ==
  /\ frontier = {}
  /\ pc = "scanning"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  /\ \/ \E n \in frontier : MarkOrRemove(n)
     \/ Terminate
  /\ WF_vars(Next)

Spec == Init /\ [][Next]_vars

Inv1 == \A n \in marked : Succ[n] \subseteq marked \cup frontier
Inv2 == (marked \cup frontier) \subseteq Nodes
Inv3 ==
  (marked \cup frontier) \cup {Root} = Nodes
  /\ {Root} \cup (marked \cup frontier) = Nodes
PartialCorrectness ==
  frontier = {} => marked = Nodes
Termination ==
  Finite ~> FrontierEmpty
FrontierEmpty == frontier = {}
====