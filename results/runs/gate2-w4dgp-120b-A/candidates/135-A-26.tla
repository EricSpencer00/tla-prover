---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"init", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = "searching"

Mark ==
  /\ pc = "searching"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup Succ[n]) \ marked \cup {n}
  /\ pc' = pc

Done ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Spec == Init /\ [][Next]_vars /\ WF_vars(Mark) /\ WF_vars(Done)

MarkingClosure ==
  \A m \in marked : \E n \in frontier : m \in Succ[n]

ReachabilityDecomposition ==
  \A n \in Nodes : (n \in marked) <=> (n \in frontier \cup {Root})

ReachableSetMatch ==
  \A n \in Nodes : (n \in marked) <=> (\E s \in LimitedSeq(Nodes) : s[1] = Root /\ s[Len(s)] = n)

PartialCorrectness ==
  \A n \in Nodes :
    (n \in marked => \E s \in LimitedSeq(Nodes) : s[1] = Root /\ s[Len(s)] = n)

Termination == <>(pc = "done")
====