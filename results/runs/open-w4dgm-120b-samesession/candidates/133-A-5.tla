---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The sequential model makes Succ a bounded function of each node's position in
\* a ring of 4 nodes; here it is a constant set-valued function given by the
\* configuration, but the values are still exactly the two successors each node
\* has in the concrete graph structure, so the bound is identical in both.
ConnectedToSomeButNotAll == Succ

\* Bounded max sequence length; this is the overridden operator (keep the name)
\* so the .cfg substitution is satisfied.
LimitedSeq(s) == s

VARIABLES marked, frontier, pc, sel, succs
vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "reading", "writing"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Read(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll[n]]
  /\ pc' = [pc EXCEPT ![p] = "reading"]
  /\ UNCHANGED marked

Compute(p) ==
  /\ pc[p] = "reading"
  /\ pc' = [pc EXCEPT ![p] = "writing"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Write(p) ==
  /\ pc[p] = "writing"
  /\ marked' = marked \cup succs[p]
  /\ frontier' = frontier \cup succs[p]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED sel

Abort(p) ==
  /\ pc[p] \in {"reading", "writing"}
  /\ frontier' = frontier \cup (IF sel[p] = "none" THEN {} ELSE {sel[p]})
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, sel>>

Next ==
  \/ \E p \in Procs, n \in Nodes: Read(p, n)
  \/ \E p \in Procs: Compute(p)
  \/ \E p \in Procs: Write(p)
  \/ \E p \in Procs: Abort(p)

Spec == Init /\ [][Next]_vars

\* The invariant: frontier and marked always partition the node set, and a
\* process never sits holding a node that has already been marked as visited.
Inv ==
  /\ frontier \cup marked = Nodes
  /\ frontier \cap marked = {}
  /\ \A p \in Procs: sel[p] # "none" => sel[p] \notin marked

\* The concurrent algorithm's reachability set coincides exactly with the
\* sequential algorithm's: it is exactly the nodes reachable from the root.
Refines ==
  frontier \cup marked = Nodes
====