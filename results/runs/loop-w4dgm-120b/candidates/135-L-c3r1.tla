---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Succ

SeqEq(s, t) == IF s \in Sequences.Seq(\X) /\ t \in Sequences.Seq(\X) THEN Sequences.EqSeq(s, t) ELSE FALSE

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ(Root)
  /\ pc = "active"

Explore(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ(n)) \ {n}
  /\ UNCHANGED pc

Complete ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes : Explore(n)
  \/ Complete

Spec == Init /\ [][Next]_vars

Inv1 ==
  frontier \subseteq {n \in Nodes : \E m \in marked : n \in Succ(m)}

Inv2 ==
  (\A A, B \in SUBSET Nodes :
     (\A m \in A, n \in Nodes : (n \in Succ(m)) => n \in B)
       => A \subseteq B) /\ (Nodes \subseteq marked)

Inv3 ==
  Nodes \subseteq {n \in Nodes :
    \E s \in Sequences.Seq(Nodes) :
      /\ s[1] = Root
      /\ s[Len(s)] = n
      /\ \A i \in 1 .. (Len(s) - 1) : s[i + 1] \in Succ(s[i])}

PartialCorrectness == \A n \in Nodes : n \in marked => n \in frontier

Termination == <>(pc = "done")

ConnectedToSomeButNotAll(n) == Succ(n)
====