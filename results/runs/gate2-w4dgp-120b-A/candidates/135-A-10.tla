---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences, Reachable

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Expand ==
  /\ pc = "running"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup Succ[n]) \ marked
  /\ pc' = IF frontier \cup Succ[n] \ marked = {} THEN "done" ELSE pc

Terminating ==
  /\ pc = "done"
  /\ UNCHANGED <<marked, frontier, pc>>

Next == Expand \/ Terminating

StateSpace == marked \cup frontier

Spec == Init /\ [][Next]_<<marked, frontier, pc>>

Inv1 ==
  \A n \in frontier : \A m \in frontier : n = m

Inv2 ==
  \A n \in frontier : \E m \in marked : n \in Succ[m]

Inv3 ==
  \A n \in marked : \E p \in Seq(Nodes) :
    /\ Length(p) <= Cardinality(Nodes)
    /\ p # <<>>
    /\ Head(p) = Root
    /\ Last(p) = n
    /\ \A i \in 1 .. (Length(p) - 1) : p[i+1] \in Succ[p[i]]

PartialCorrectness ==
  StateSpace \subseteq marked

SuccFor == \E m \in Nodes : Succ[m]

Termination == <>(pc = "done")

====