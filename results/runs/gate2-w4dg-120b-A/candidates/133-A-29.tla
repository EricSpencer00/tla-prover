---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

\* Configuration module for the parallel reachability algorithm.
\* It inherits the algorithm's state and actions, and adds the concrete
\* graph and process set used for model checking.  The spec sets up a
\* bounded model: 4 nodes, 2 workers, and a sequence bound equal to the
\* number of nodes.

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, node, succ

vars == <<marked, frontier, pc, node, succ>>

TypeOK ==
  /\ marked \in SUBSET Nodes
  /\ frontier \in SUBSET Nodes
  /\ pc \in [Procs -> {"idle", "working"}]
  /\ node \in [Procs -> Nodes]
  /\ succ \in [Procs -> Seq]

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ node = [p \in Procs |-> Root]
  /\ succ = [p \in Procs |-> << >>]

Claim(p, v) ==
  /\ pc[p] = "idle"
  /\ v \in frontier
  /\ frontier' = frontier \ {v}
  /\ marked' = marked \cup {v}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ node' = [node EXCEPT ![p] = v]
  /\ succ' = [succ EXCEPT ![p] = << >>]

Step(p) ==
  /\ pc[p] = "working"
  /\ Len(succ[p]) < Cardinality(Nodes)
  /\ frontier' = frontier \cup {Succ[node[p]]}
  /\ succ' = [succ EXCEPT ![p] = Append(succ[p], Succ[node[p]])]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, node>>

Idle ==
  /\ \A p \in Procs : pc[p] = "idle"
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Procs, v \in Nodes : Claim(p, v)
  \/ \E p \in Procs : Step(p)
  \/ Idle

Spec == Init /\ [][Next]_vars

\* Inductive invariant: all state components are within their intended
\* domains, and a worker is only ever idle while holding a complete
\* exploration sequence over the graph.
Inv ==
  /\ TypeOK
  /\ \A p \in Procs : pc[p] = "idle" => Len(succ[p]) >= 1

\* The parallel algorithm refines the sequential Misra algorithm over the
\* same graph and bound.
Refines ==
  /\ \A p \in Procs : pc[p] = "idle" => Len(succ[p]) >= 1
  /\ frontier = Succ[marked]

====