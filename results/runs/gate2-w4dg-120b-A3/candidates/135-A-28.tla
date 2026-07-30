---- MODULE MCReachable ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Succ

VARIABLES mark, frontier, pc

vars == <<mark, frontier, pc>>

TypeOK ==
  /\ mark \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"idle", "working", "done"}

Init ==
  /\ mark = {Root}
  /\ frontier = {Root}
  /\ pc = "working"

Expand ==
  /\ pc = "working"
  /\ frontier # {}
  /\ \E n \in frontier:
       /\ n \in mark
       /\ frontier' = (frontier \ {n}) \cup (Succ[n] \ {n})
       /\ mark' = mark \cup Succ[n]
  /\ UNCHANGED pc

Finish ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<mark, frontier>>

Spec == Init /\ [][Expand]_vars /\ WF_vars(Finish)

Inv1 == frontier \subseteq mark
Inv2 == mark \subseteq ConnectedToSomeButNotAll[Root]
Inv3 == mark = ConnectedToSomeButNotAll[Root]

Termination == <>(pc = "done")

PartialCorrectness ==
  /\ \A x \in mark : \E p \in LimitedSeq[Nodes] : p # <<>> /\ Head(p) = Root /\ Last(p) = x
  /\ \A x \in Nodes : \A p \in LimitedSeq[Nodes] : (p # <<>> /\ Head(p) = Root /\ Last(p) = x) => x \in mark

ConnectedToSomeButNotAll[n] ==
  LET NextAll(m) == \E k \in Nodes : m \in Succ[k] /\ k \notin Nodes
  IN
  {x \in Nodes : \E p \in LimitedSeq[Nodes] : p # <<>> /\ Head(p) = n /\ Last(p) = x}

LimitedSeq[U] == {s \in Seq(U) : Len(s) <= Cardinality(Nodes)}

====