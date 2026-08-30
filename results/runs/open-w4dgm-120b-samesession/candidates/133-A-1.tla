---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES frontier, marked, pc, selected, succs

TypeOK ==
  /\ frontier \in Seq(Nodes)
  /\ marked \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "done"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Nodes -> SUBSET Nodes]

Init ==
  /\ frontier = << >>
  /\ marked = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = Succ

Begin(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ selected' = [selected EXCEPT ![p] = Root]
  /\ succs' = succs
  /\ marked' = marked
  /\ frontier' = frontier

Select(p, n) ==
  /\ pc[p] = "selecting"
  /\ selected[p] \in Nodes
  /\ n \in succs[selected[p]]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ pc' = pc
  /\ succs' = succs
  /\ marked' = marked
  /\ frontier' = frontier

Mark(p) ==
  /\ pc[p] = "selecting"
  /\ selected[p] \in Nodes
  /\ selected[p] \notin marked
  /\ Cardinality(frontier) < Cardinality(Nodes)
  /\ marked' = marked \cup {selected[p]}
  /\ frontier' = Append(frontier, selected[p])
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ selected' = selected
  /\ succs' = succs

Skip(p) ==
  /\ pc[p] = "selecting"
  /\ selected[p] \in Nodes
  /\ selected[p] \in marked
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ selected' = selected
  /\ frontier' = frontier
  /\ marked' = marked
  /\ succs' = succs

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ frontier' = frontier
  /\ marked' = marked
  /\ succs' = succs

Next ==
  \/ \E p \in Procs : Begin(p)
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Skip(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_<<frontier, marked, pc, selected, succs>>

ControlFlowRespected ==
  /\ \A p \in Procs : (pc[p] = "selecting") => (selected[p] \in Nodes)
  /\ \A p \in Procs : (pc[p] = "done") => (selected[p] \in Nodes \cup {"none"})
  /\ \A p \in Procs : (pc[p] = "idle") => (selected[p] = "none")

Refines == ControlFlowRespected

Inv == TypeOK /\ ControlFlowRespected

ConnectedToSomeButNotAll ==
  \E m \in Nodes :
    /\ \E s \in Succ : s # {}
    /\ \A s \in Succ : s \subseteq Nodes
    /\ \A x, y \in Nodes : (x \in s /\ y \in s) => (x = y)

LimitedSeq == (Seq \X {}) \cup (FiniteSets \X (SUBSET Nodes))

====