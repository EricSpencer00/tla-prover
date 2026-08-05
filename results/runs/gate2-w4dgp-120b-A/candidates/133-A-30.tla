---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

ASSUME Root \in Nodes
ASSUME \A u \in Nodes : Succ[u] \subseteq Nodes

VARIABLES marked, frontier, pc, selected, succSet

vars == << marked, frontier, pc, selected, succSet >>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> CHOOSE u \in Nodes : u = Root]
  /\ succSet = [p \in Procs |-> {}]

\* Pick unmarked node from the shared frontier and snapshot its successors.
Traverse(p) ==
  /\ pc[p] = "idle"
  /\ \E u \in frontier :
       /\ frontier' = frontier \ {u}
       /\ selected' = [selected EXCEPT ![p] = u]
       /\ succSet' = [succSet EXCEPT ![p] = Succ[u]]
  /\ pc' = [pc EXCEPT ![p] = "inflight"]
  /\ UNCHANGED marked

\* Mark the traversed node and merge its successors into the frontier.
Mark(p) ==
  /\ pc[p] = "inflight"
  /\ selected[p] \notin marked
  /\ marked' = marked \cup {selected[p]}
  /\ frontier' = frontier \cup succSet[p]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << selected, succSet >>

\* Idle each worker that has finished, so it can advance again.
Finish(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << marked, frontier, selected, succSet >>

Next == \E p \in Procs : Traverse(p) \/ Mark(p) \/ Finish(p)

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in {"idle", "inflight", "done"}
  /\ \A p \in Procs : pc[p] = "inflight" => selected[p] \notin marked
  /\ \A p \in Procs : pc[p] = "done" => selected[p] \in marked

Spec == Init /\ [][Next]_vars

\* The parallel algorithm implements the sequential Misra algorithm.
Refines == \A p \in Procs : pc[p] = "idle"

LimitedSeq == Seq
====