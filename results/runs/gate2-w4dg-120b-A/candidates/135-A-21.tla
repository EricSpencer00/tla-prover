---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Completed == frontier = {}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "running"

StepMark ==
  /\ frontier # {}
  /\ \E x \in frontier :
       /\ marked' = marked \cup {x}
       /\ frontier' = (frontier \cup Succ[x]) \ {x}
  /\ pc' = "running"

StepDone ==
  /\ frontier = {}
  /\ pc = "running"
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ StepMark
  \/ StepDone

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \/ frontier = {}
  \/ \E n \in frontier : \E m \in marked : n \in Succ[m]

Inv2 ==
  /\ marked \subseteq (Root \cup frontier)
  /\ frontier \subseteq (Nodes \marked)

Inv3 ==
  \A n \in Nodes : \E s \in Seq : s # <<>> /\ Head(s) = Root /\ Last(s) = n /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in Succ[s[i]]

PartialCorrectness ==
  frontier = {} => marked = Nodes

Termination ==
  <>(pc = "done")

====