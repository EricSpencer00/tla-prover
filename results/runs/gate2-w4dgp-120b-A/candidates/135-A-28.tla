---- MODULE MCReachable ----
EXTENDS Naturals, Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "done"}

Inv1 ==
  /\ frontier = (IF Root \in marked THEN {} ELSE {Root})
  /\ marked \cap frontier = {}

Inv2 == \A n \in frontier : \E m \in marked : n \in ConnectedToSomeButNotAll[m]

Inv3 == \A n \in Nodes : n \in marked => n \in ConnectedToSomeButNotAll[n]

PartialCorrectness ==
  \A n \in Nodes : n \in marked => n \in ConnectedToSomeButNotAll[Root]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = "idle"

Step ==
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \ {n}) \cup \{ m \in Nodes : m \in ConnectedToSomeButNotAll[n] /\ m \notin marked \}
  /\ pc' = "idle"

Done ==
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next == Step \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(Step)

Termination == <>(pc = "done")

====