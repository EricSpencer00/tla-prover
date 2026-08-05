---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs
vars == <<marked, frontier, pc, selected, succs>>

Seq == << >>
LimitedSeq == (Seq) \cup {s \in Seq : Len(s) <= Cardinality(Nodes)}

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Mark(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ selected' = [selected EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<marked, succs>>

Explore(p) ==
  /\ pc[p] = "working"
  /\ succs' = [succs EXCEPT ![p] = Succ[selected[p]]]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, selected>>

Collect(p) ==
  /\ pc[p] = "done"
  /\ \E n \in succs[p] :
       /\ ~ \E q \in Procs : selected[q] = n
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup {n}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ UNCHANGED <<selected>>

Next == \E p \in Procs : Mark(p) \/ Explore(p) \/ Collect(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == FrontierIsSubsetOfReachable

FrontierIsSubsetOfReachable ==
  frontier \subseteq (Nat \ {0}) /\
  \A i \in 0..(Nat - 1) : FrontierAtStep(i) \subseteq ReachableAtStep(i)

ReachableAtStep(n) ==
  IF n = 0 THEN {Root}
  ELSE IF n = 1 THEN
    {Root} \cup Succ[Root]
  ELSE
    {Root} \cup Succ[Root] \cup Succ[Succ[Root]]

FrontierAtStep(n) ==
  IF n = 0 THEN {Root}
  ELSE IF n = 1 THEN Succ[Root]
  ELSE Succ[Succ[Root]]

Nat == Cardinality(Nodes)
====