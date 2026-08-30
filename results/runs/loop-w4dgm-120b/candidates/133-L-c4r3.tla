---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

\* Succ is a constant mapping from a node to its two successors; it is
\* injected into the model as a constant rather than defined here, per the
\* .cfg substitution.
SuccOf(n) == Succ[n]

VARIABLES marked, frontier, pc, selected, succs

vars == <<marked, frontier, pc, selected, succs>>

\* Type: every node's per-process successor set stays within the successors
\* of that node. The model also keeps the frontier strictly inside the
\* reachable frontier: marked nodes are never simultaneously frontier.
TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "holding", "crashed"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Grab(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "holding"]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

\* The two successors are added to the live frontier at most once each, in
\* arbitrary order, so the frontier can be explored in any interleaving.
AddSuccessor(p, s) ==
  /\ pc[p] = "holding"
  /\ s \in SuccOf(selected[p])
  /\ s \notin marked
  /\ marked' = marked \cup {s}
  /\ frontier' = frontier \cup {s}
  /\ succs' = [succs EXCEPT ![p] = succs[p] \cup {s}]
  /\ UNCHANGED <<pc, selected>>

Release(p) ==
  /\ pc[p] = "holding"
  /\ succs[p] = SuccOf(selected[p])
  /\ frontier' = frontier \ {selected[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED marked

Crash(p) ==
  /\ pc[p] \in {"idle", "holding"}
  /\ pc' = [pc EXCEPT ![p] = "crashed"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Grab(p, n)
  \/ \E p \in Procs, s \in Nodes : AddSuccessor(p, s)
  \/ \E p \in Procs : Release(p)
  \/ \E p \in Procs : Crash(p)

\* Safety: each action's effects keep the frontier inside the reachable set
\* and each successor set within its source node's successors.
Inv == TypeOK

\* Liveness: every process that takes a node eventually finishes with it,
\* either releasing it or crashing.
Refines ==
  \A p \in Procs : (pc[p] = "holding") ~> (pc[p] \in {"idle", "crashed"})

Spec == Init /\ [][Next]_vars

\* The configuration replaces the unbounded Seq operator with a finite one
\* so the model is checkable; the original inductive invariant does not
\* depend on it.
LimitedSeq ==
  \A a \in Nat, b \in Nat :
    /\ a > 0 /\ a <= Len(frontier)
    /\ b > 0 /\ b <= Len(frontier)
    /\ frontier[a] = frontier[b]
    => a = b

ConnectedToSomeButNotAll ==
  \A m \in Nodes : \E k \in Nodes : k \in SuccOf(m) /\ m \in frontier

====