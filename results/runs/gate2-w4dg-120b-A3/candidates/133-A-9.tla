---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

ASSUME Root \in Nodes
ASSUME Succ \subseteq [Nodes -> Nodes]

VARIABLES marked, frontier, pc, sel, succs

vars == << marked, frontier, pc, sel, succs >>

RECURSIVE SuccSet(_)
SuccSet(n) ==
  IF n \in Nodes
  THEN LET rs == Succ[n] IN
       IF rs = {} THEN {} ELSE {n} \cup SuccSet(<< rs >>)
  ELSE {}

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "select", "claim", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = SuccSet(Root)
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

SelectNode(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "select"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED << marked, succs >>

ClaimNode(p) ==
  /\ pc[p] = "select"
  /\ pc' = [pc EXCEPT ![p] = "claim"]
  /\ succs' = [succs EXCEPT ![p] = Succ[sel[p]]]
  /\ UNCHANGED << marked, frontier, sel >>

MarkNode(p, n) ==
  /\ pc[p] = "claim"
  /\ n \in succs[p]
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup SuccSet(n)
  /\ succs' = [succs EXCEPT ![p] = succs[p] \ {n}]
  /\ UNCHANGED << pc, sel >>

Done(p) ==
  /\ pc[p] = "claim"
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED << marked, frontier, sel >>

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED << marked, frontier, succs >>

Next ==
  \/ \E p \in Procs, n \in Nodes : SelectNode(p, n)
  \/ \E p \in Procs : ClaimNode(p) \/ Done(p) \/ Reset(p)
  \/ \E p \in Procs, n \in Nodes : MarkNode(p, n)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ TypeOK
  /\ Root \in marked
  /\ \A p \in Procs : pc[p] \in {"idle", "select", "claim", "done"}
  /\ \A p \in Procs : (pc[p] = "claim") => (sel[p] \in Nodes)

Refines == Inv

ConnectedToSomeButNotAll(n) ==
  /\ n \in Nodes
  /\ \E m \in Nodes : m \in Succ[n] /\ m \notin Succ[n]

LimitedSeq(_)
====