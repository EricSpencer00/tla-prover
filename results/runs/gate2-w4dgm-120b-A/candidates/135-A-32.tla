---- MODULE MCReachable ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANT Nodes, Root, Succ

AllNodes == Nodes

VARIABLES marked, frontier, pc

vars == <<marked, frontier, pc>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ(Root)
  /\ pc = "Marking"

MarkStep ==
  /\ pc = "Marking"
  /\ \E n \in frontier :
       /\ marked' = marked \cup {n}
       /\ frontier' = (frontier \cup Succ(n)) \ marked
  /\ pc' = pc

Stop ==
  /\ pc = "Marking"
  /\ frontier = {}
  /\ pc' = "Done"
  /\ UNCHANGED <<marked, frontier>>

Reset ==
  /\ pc = "Done"
  /\ marked' = {Root}
  /\ frontier' = Succ(Root)
  /\ pc' = "Marking"

Next == MarkStep \/ Stop \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Stop) /\ WF_vars(Reset)

TypeOK ==
  /\ marked \subseteq AllNodes
  /\ frontier \subseteq AllNodes
  /\ pc \in {"Marking", "Done"}

Inv1 ==
  frontier \subseteq (AllNodes \ marked)

Inv2 ==
  (marked \cup frontier) = AllNodes

Inv3 ==
  \A n \in marked : n = Root \/ \E m \in marked : n \in Succ(m)

PartialCorrectness ==
  \A n \in AllNodes : (\E m \in marked : n \in Succ(m)) => n \in marked

Termination ==
  <>(pc = "Done")

ConnectedToSomeButNotAll(n) ==
  Succ(n)

LimitedSeq(S) ==
  IF Len(S) = Cardinality(AllNodes) THEN S ELSE <<>>

====