---- MODULE MCReachable ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANT Nodes
CONSTANT Root
CONSTANT Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "active"

Mark(n) ==
  /\ pc = "active"
  /\ n \in frontier
  /\ marked' = marked \cup {n}
  /\ frontier' = (frontier \cup Succ[n]) \ {n}
  /\ pc' = pc

Finish ==
  /\ pc = "active"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Restart ==
  /\ pc = "done"
  /\ frontier = {}
  /\ frontier' = {}
  /\ marked' = {}
  /\ pc' = "active"

Next ==
  \/ \E n \in Nodes : Mark(n)
  \/ Finish
  \/ Restart

Spec == Init /\ [][Next]_vars /\ WF_vars(Restart)

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"active", "done"}

Inv1 ==
  \A n \in frontier : n \notin marked

Inv2 ==
  \A m \in marked : m = Root \/ \E p \in Nodes : m \in Succ[p]

Inv3 ==
  \A n \in Nodes : n \in marked => \E seq \in LimitedSeq(Nodes) : IsReachable(seq, n)

PartialCorrectness ==
  \A n \in Nodes : IsReachable(<<Root>>, n) => n \in marked

Termination == <>(pc = "done")

IsReachable(seq, n) ==
  /\ Len(seq) >= 1
  /\ Head(seq) = Root
  /\ \A i \in 1..(Len(seq) - 1) : seq[i + 1] \in Succ[seq[i]]
  /\ seq[Len(seq)] = n

LimitedSeq(S) ==
  { f \in Seq(S) : Len(f) <= Cardinality(Nodes) }

ConnectedToSomeButNotAll(n) == Succ[n]

====