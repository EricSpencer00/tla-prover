---- MODULE MCReachable ----
EXTENDS Integers, Sequences

CONSTANT Nodes, Root, Succ

ASSUME Succ \in [Nodes -> SUBSET Nodes]
ASSUME Cardinality(Nodes) = 4
ASSUME Root \in Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "active"

Explore(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ frontier' = (frontier \cup Succ[n]) \ marked
  /\ marked' = marked \cup {n}
  /\ UNCHANGED pc

Finish ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Abort ==
  /\ pc = "active"
  /\ pc' = "aborted"
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E n \in Nodes: Explore(n)
  \/ Finish
  \/ Abort

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done", "aborted"}

Inv1 ==
  frontier \cap marked = {}

Inv2 ==
  \A a \in marked, b \in marked : (a # b) => (b \in Succ[a])

Inv3 ==
  \A n \in marked : \E seq \in LimitedSeq(Nodes) :
    /\ seq[1] = Root
    /\ seq[Len(seq)] = n
    /\ \A i \in 1..(Len(seq) - 1) : seq[i+1] \in Succ[seq[i]]

PartialCorrectness ==
  \A n \in marked : \E seq \in LimitedSeq(Nodes) :
    /\ seq[1] = Root
    /\ seq[Len(seq)] = n
    /\ \A i \in 1..(Len(seq) - 1) : seq[i+1] \in Succ[seq[i]]

Termination ==
  \A <> (pc \in {"done", "aborted"})

ConnectedToSomeButNotAll ==
  {n \in Nodes : Cardinality(Succ[n]) > 0 /\ Cardinality(Succ[n]) < Cardinality(Nodes)}

LimitedSeq(S) ==
  {s \in Seq(S) : Len(s) <= Cardinality(S)}
====