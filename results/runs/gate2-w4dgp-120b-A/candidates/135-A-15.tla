---- MODULE MCReachable ----
EXTENDS FiniteSets, Sequences, Naturals

CONSTANTS Nodes, Root, Succ

ASSUME Root \in Nodes
ASSUME Succ \in [Nodes -> SUBSET Nodes]

VARIABLES marked, frontier, pc
vars == <<marked, frontier, pc>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in {"idle", "searching", "done"}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = "idle"

Neighbor(n) == CHOOSE x \in Succ[n] : TRUE

SuccessorClosure ==
  \A n \in frontier : marked' = marked \cup {Neighbor(n)} /\ frontier' = frontier \cup {Neighbor(n)}
  /\ pc' = "searching"

StartSearch ==
  /\ pc = "idle"
  /\ frontier # {}
  /\ pc' = "searching"
  /\ UNCHANGED <<marked, frontier>>

Complete ==
  /\ pc = "searching"
  /\ frontier = {}
  /\ pc' = "done"
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ pc = "done"
  /\ UNCHANGED vars

Next == StartSearch \/ SuccessorClosure \/ Complete \/ Done

Spec == Init /\ [][Next]_vars /\ WF_vars(StartSearch) /\ WF_vars(SuccessorClosure) /\ WF_vars(Complete)

Inv1 == frontier \subseteq marked

Inv2 == marked \subseteq Nodes

Inv3 == (\E s \in Seq(Nodes) : Head(s) = Root /\ marked = {s[i] : i \in 1..Len(s)}) /\ (pc = "done" => frontier = {})

PartialCorrectness == (pc = "done") => (marked = Nodes)

Termination == <>(pc = "done")

ConnectedToSomeButNotAll == Succ

LimitedSeq == {s \in Seq(Nodes) : Len(s) <= Cardinality(Nodes)}

====