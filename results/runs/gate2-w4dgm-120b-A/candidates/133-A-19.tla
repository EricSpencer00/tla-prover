---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

SuccSet(n) == Succ[n]

VARIABLES marked, frontier, pc, sel, succs

vars == << marked, frontier, pc, sel, succs >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = SuccSet(Root)
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ n \notin marked
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = SuccSet(n)]
  /\ UNCHANGED << marked, frontier >>

AddSuccessor(p, m) ==
  /\ pc[p] = "working"
  /\ m \in succs[p]
  /\ frontier' = frontier \cup {m}
  /\ succs' = [succs EXCEPT ![p] = succs[p] \ {m}]
  /\ UNCHANGED << marked, pc, sel >>

Mark(p) ==
  /\ pc[p] = "working"
  /\ succs[p] = {}
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = frontier \ {sel[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED sel

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, m \in Nodes : AddSuccessor(p, m)
  \/ \E p \in Procs : Mark(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \cap frontier = {}
  /\ marked \cup frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] = "working" => sel[p] \in frontier
  /\ \A p \in Procs : pc[p] = "working" => succs[p] \subseteq succs[p] \cup frontier

Refines ==
  /\ \A n \in Nodes : (n \in marked) <=> (\A p \in Procs : (pc[p] = "working" /\ sel[p] = n) \/ n \in succs[p])
  /\ \A p \in Procs : pc[p] = "working" => sel[p] \in frontier

LimitedSeq == Seq

====