---- MODULE MCReachable ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, ConnectedToSomeButNotAll

\* The reachable-set condition is expressed as a nested existential instead of
\* an explicit path, so the override below is the only thing keeping the
\* reachable-set check finite.
Sequence == {s \in Seq(Nodes) : Length(s) <= Cardinality(Nodes)}

VARIABLES marked, frontier, pc, retry

vars == <<marked, frontier, pc, retry>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in {"idle", "working", "done"}
  /\ retry \in Nat

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"
  /\ retry = 0

\* The stepwise frontier expansion of the sequential algorithm.
Step ==
  /\ pc = "working"
  /\ frontier # {}
  /\ \E n \in frontier : frontier' = (frontier \ {n}) \cup ConnectedToSomeButNotAll[n]
  /\ marked' = marked \cup ConnectedToSomeButNotAll[n]
  /\ UNCHANGED <<pc, retry>>

Complete ==
  /\ pc = "working"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier, retry>>

Retry ==
  /\ pc = "done"
  /\ marked = Nodes
  /\ retry = 0
  /\ retry' = 1
  /\ UNCHANGED <<marked, frontier, pc>>

Reset ==
  /\ pc = "done"
  /\ pc' = "idle"
  /\ marked' = {Root}
  /\ frontier' = {Root}
  /\ UNCHANGED retry

Start == /\ pc = "idle" /\ pc' = "working" /\ UNCHANGED <<marked, frontier, retry>>

Next == Start \/ Step \/ Complete \/ Retry \/ Reset

Spec == Init /\ [][Next]_vars /\ WF_vars(Step) /\ WF_vars(Complete)

\* Every marked node is on some reachable path from the root (bounded sequence).
Inv3 ==
  /\ \A n \in marked :
       \E s \in Sequence :
         /\ Len(s) > 0
         /\ s[1] = Root
         /\ s[Len(s)] = n
         /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in ConnectedToSomeButNotAll[s[i]]
  /\ \A n \in frontier : n \notin marked

Inv1 == frontier \subseteq Nodes \ marked
Inv2 == marked \subseteq {n \in Nodes : \E s \in Sequence : Len(s) > 0 /\ s[1] = Root /\ s[Len(s)] = n /\ \A i \in 1..(Len(s) - 1) : s[i+1] \in ConnectedToSomeButNotAll[s[i]]}
Termination == <>(pc = "done")
PartialCorrectness == Nodes \subseteq marked

====