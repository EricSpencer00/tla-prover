---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "searching"

Step ==
  /\ pc = "searching"
  /\ \E y \in frontier :
       /\ y \notin marked
       /\ marked' = marked \cup {y}
       /\ frontier' = (frontier \cup Succ[y]) \ {y}
  /\ UNCHANGED pc

Terminate ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == Step \/ Terminate \/ Done

Spec == Init /\ [][Next]_vars

Inv1 == marked \subseteq Nodes

Inv2 ==
  \A x \in Nodes :
    /\ x \in marked => \E y \in frontier : x \in Succ[y]
    /\ x \notin marked => x \notin frontier

Inv3 == marked \cup frontier = Nodes

PartialCorrectness == \A x \in Nodes : (x \in marked) <=> (x \in Reach(Root, Nodes, Succ))

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ

LimitedSeq == {s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes)}
====