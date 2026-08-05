---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "exploring", "done"}

Inv1 ==
  \A a \in Nodes :
    a \in frontier => (\E b \in Nodes : a \in Succ[b])

Inv2 ==
  \A s \in Nodes :
    s \in marked =>
      (\E t \in Nodes : \E p \in LimitedSeq(Nodes) :
        Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = s /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]))

Inv3 ==
  \A s \in Nodes :
    s \in marked <=> (\E t \in Nodes : \E p \in LimitedSeq(Nodes) :
      Len(p) > 0 /\ p[1] = Root /\ p[Len(p)] = s /\ \A i \in 1..(Len(p) - 1) : p[i+1] \in Succ[p[i]]))

PartialCorrectness == frontier \subseteq marked

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "idle"

ExploreStep ==
  /\ pc \in {"idle", "exploring"}
  /\ frontier # {}
  /\ \E e \in frontier :
       /\ marked' = marked \cup {e}
       /\ frontier' = (frontier \cup Succ[e]) \ {e}
  /\ pc' = "exploring"

Finish ==
  /\ pc \in {"idle", "exploring"}
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ ExploreStep
  \/ Finish

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "done")

====