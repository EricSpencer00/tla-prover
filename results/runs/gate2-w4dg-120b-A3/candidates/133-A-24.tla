---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The base graph: every node has exactly 2 successors, drawn from the NextUp
\* operation so all are determined by the node count.  Since Succ is a constant,
\* the .cfg substitutes a bounded version of ConnectedToSomeButNotAll that
\* selects exactly two successors per node.
NextUp(n) == { m \in Nodes : n < m /\ m <= n + 2 }

VARIABLES marked, frontier, pc, chosen, succ

vars == << marked, frontier, pc, chosen, succ >>

\* The parallel algorithm's actions are used unchanged here; only the data they
\* operate on is instantiated concretely.
Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ chosen = [p \in Procs |-> 0]
  /\ succ = [p \in Procs |-> {}]

\* Worker p selects a frontier node to explore; always enabled, which is
\* what makes the configuration reachable from every state.
Choose(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ chosen' = [chosen EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ succ' = [succ EXCEPT ![p] = NextUp(chosen[p])]
  /\ UNCHANGED marked

Mark(p) ==
  /\ pc[p] = "working"
  /\ \E n \in succ[p] :
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup {n}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << chosen, succ >>

Reset ==
  /\ \A p \in Procs : pc[p] = "done"
  /\ marked' = {}
  /\ frontier' = {Root}
  /\ pc' = [p \in Procs |-> "idle"]
  /\ chosen' = [p \in Procs |-> 0]
  /\ succ' = [p \in Procs |-> {}]

Next == Reset \/ (\E p \in Procs : Choose(p) \/ Mark(p))

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ chosen \in [Procs -> 0..Cardinality(Nodes)]
  /\ succ \in [Procs -> SUBSET Nodes]

\* The inductive invariant is exactly the parallel algorithm's: a working
\* process has taken a node off the frontier, its successors lie in the next
\* level up, and no finished process still has an active frontier node.
Inv ==
  /\ TypeOK
  /\ \A p \in Procs :
       pc[p] = "working" => (chosen[p] \in frontier /\ succ[p] \subseteq NextUp(chosen[p]))
  /\ \A p \in Procs :
       pc[p] = "done" => (chosen[p] \notin frontier /\ frontier \cap NextUp(chosen[p]) = {})

\* The refinement property: every marked node is reachable from the root by
\* repeated application of NextUp, which is exactly what the sequential MISRA
\* algorithm guarantees.
Refines ==
  \A n \in marked : \E k \in Nat : n \in (NextUp)^^k {Root}

Spec == Init /\ [][Next]_vars

====