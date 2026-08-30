---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

ProgramCounter == {"idle", "finding", "done"}
Factory == {"frontier", "marked", "none"}

VARIABLES marked, frontier, pc, target

vars == <<marked, frontier, pc, target>>

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = "finding"
  /\ target = Root

Traverse(n) ==
  /\ pc = "finding"
  /\ n \in Succ[target]
  /\ n # target
  /\ target' = n
  /\ UNCHANGED <<marked, frontier, pc>>

Explore(n) ==
  /\ pc = "finding"
  /\ n \in Succ[target]
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup {n}
  /\ UNCHANGED <<pc, target>>

CloseNode(n) ==
  /\ pc = "finding"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<marked, pc, target>>

Settle ==
  /\ pc = "finding"
  /\ frontier = {}
  /\ target = Root
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier, target>>

Idle ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next ==
  \/ \E n \in Nodes : Traverse(n)
  \/ \E n \in Nodes : Explore(n)
  \/ \E n \in Nodes : CloseNode(n)
  \/ Settle
  \/ Idle

Spec == Init /\ [][Next]_vars /\ WF_vars(Traverse(Root))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in ProgramCounter
  /\ target \in Nodes

Inv1 ==
  \A n \in frontier : n \in marked

Inv2 ==
  frontier \cup marked = Nodes

Inv3 ==
  \A n \in Nodes : (n \in marked) ~> (n \in marked)

PartialCorrectness ==
  (pc = "done") ~> (pc = "done")

Termination == (pc = "finding") ~> (pc = "done")

ConnectedToSomeButNotAll(n) == Succ[n]

LimitedSeq(S) == CHOOSE s \in Seq(S) : Len(s) = Cardinality(S)

====