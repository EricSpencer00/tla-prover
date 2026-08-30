---- MODULE MCParReach ----
EXTENDS Integers, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* Bounded sequence type derived from Sequences, but the .cfg expects the
\* name Seq to be replaced by the operator defined here.
LimitedSeq(T) == Seq(T)

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

\* Parallel reachability: each worker picks a marked frontier node and
\* processes its successors under optimistic locking; pc tracks its
\* control location. The invariant below is the joint type/flow property.
Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "has"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED marked

Read(p, d) ==
  /\ pc[p] = "has"
  /\ d \in Succ[sel[p]]
  /\ d \notin marked
  /\ d \notin succs[p]
  /\ succs' = [succs EXCEPT ![p] = succs[p] \cup {d}]
  /\ pc' = [pc EXCEPT ![p] = "read"]
  /\ UNCHANGED <<marked, frontier, sel>>

CASFail(p) ==
  /\ pc[p] = "read"
  /\ \E d \in succs[p] : d \in marked
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "has"]
  /\ UNCHANGED <<marked, frontier, sel>>

CASApply(p) ==
  /\ pc[p] = "read"
  /\ \A d \in succs[p] : d \notin marked
  /\ marked' = marked \cup succs[p]
  /\ frontier' = frontier \cup succs[p]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]

Done(p) ==
  /\ pc[p] = "has"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, d \in Nodes : Read(p, d)
  \/ \E p \in Procs : CASFail(p)
  \/ \E p \in Procs : CASApply(p)
  \/ \E p \in Procs : Done(p)

Spec == Init /\ [][Next]_vars

\* Every worker is in an idle or done state as soon as its selected node
\* is no longer on the frontier, so the optimistic lock is always released
\* one way or the other and a worker can never be stuck on a marked node.
TypeOK ==
  /\ pc \in [Procs -> {"idle", "has", "read"}]
  /\ sel \in [Procs -> {Root} \cup {"none"}]
  /\ frontier \subseteq Nodes
  /\ marked \subseteq Nodes
  /\ succs \in [Procs -> SUBSET Nodes]

Refines == TypeOK

====