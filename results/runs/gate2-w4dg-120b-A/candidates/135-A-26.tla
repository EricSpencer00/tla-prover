---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ, Seq

VARIABLES marked, frontier, pc

vars == << marked, frontier, pc >>

Init == /\ marked = {Root}
        /\ frontier = Succ[Root]
        /\ pc = "exploring"

Explore == /\ frontier # {}
          /\ \E x \in frontier :
               /\ marked' = marked \cup {x}
               /\ frontier' = (frontier \cup Succ[x]) \ {x}
          /\ pc' = "exploring"

Terminate == /\ frontier = {}
             /\ pc' = "done"
             /\ UNCHANGED << marked, frontier >>

Next == Explore \/ Terminate

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"exploring", "done"}

Inv1 == frontier \subseteq (Nodes \ marked)

Inv2 == marked = UNION {Seq[i] : i \in DOMAIN Seq}

Inv3 == \A u \in Nodes : u \in marked <=> \E p \in Seq : p[1] = Root /\ p[Len(p)] = u

PartialCorrectness == \A u \in Nodes : u \in marked => Reachable(Root, u)

Termination == <>(pc = "done")

Reachable(a, b) ==
  \E p \in Seq : /\ Len(p) <= Cardinality(Nodes)
                    /\ p[1] = a
                    /\ p[Len(p)] = b
                    /\ \A i \in 1..(Len(p) - 1) : p[i + 1] \in Succ[p[i]]
====