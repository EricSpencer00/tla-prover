---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "running"

Mark(n) ==
  /\ pc = "running"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ marked' = marked \cup {n}
  /\ \E m \in Succ[n] : frontier' = frontier' \cup {m}
  /\ UNCHANGED pc

Halt ==
  /\ pc = "running"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Quiesce ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Mark(n)
  \/ Halt
  \/ Quiesce

Spec == Init /\ [][Next]_vars /\ WF_vars(Quiesce)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"running", "done"}

Inv1 ==
  \A n \in frontier : n \in marked

Inv2 ==
  \A a \in marked : (MarkedExceptRoot(a) => \E m \in Succ[a] : m \in marked)
    where MarkedExceptRoot(n) == n \in marked /\ n # Root

Inv3 ==
  \A a \in marked : \E seq \in LimitedSeq(Nodes) : seq[1] = Root /\ seq[Len(seq)] = a

PartialCorrectness ==
  Cardinality(marked) = Cardinality(Nodes)

Termination ==
  (\A n \in Nodes : n \in marked) ~> (\A n \in Nodes : n \in marked)

ConnectedToSomeButNotAll(m) ==
  Cardinality(m) >= 2 /\ Cardinality(m) < Cardinality(Nodes

====