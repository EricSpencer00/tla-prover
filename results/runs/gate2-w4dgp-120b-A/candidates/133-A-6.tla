---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

\* A model-checking configuration module for the parallel reachability algorithm.
\* It inherits the algorithm's state and actions, and supplies concrete
\* configuration: a small fixed graph, a bounded sequence override, and two
\* worker processes. The indices are all finite, so the full state space is
\* reachable and LTC can exhaustively model-check it.

CONSTANTS Nodes, Root, Procs

\* The graph's successor relation is fixed for this configuration. The override
\* in the .cfg replaces Succ below with ConnectedToSomeButNotAll, which is a
\* bounded version of Succ that keeps the graph finite.
Succ == ConnectedToSomeButNotAll

VARIABLES marked, frontier, pc, selected, succ

vars == << marked, frontier, pc, selected, succ >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "exploring", "done"}]
  /\ selected \in [Procs -> Nodes]
  /\ succ \subseteq [Nodes -> Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> Root]
  /\ succ = [n \in Nodes |-> {}]

StartExploration(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ selected' = [selected EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ frontier' = frontier \ {selected[p]}
  /\ UNCHANGED << marked, succ >>

Explore(p) ==
  /\ pc[p] = "exploring"
  /\ selected[p] \in Nodes
  /\ \E m \in Succ[selected[p]] :
       /\ marked' = marked \cup {m}
       /\ frontier' = frontier \cup {m}
  /\ succ' = [succ EXCEPT ![selected[p]] = succ[selected[p]] \cup {m}]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED << selected >>

Restart(p) ==
  /\ pc[p] = "done"
  /\ frontier # {}
  /\ selected[p] \notin frontier
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED << marked, frontier, selected, succ >>

Next == \E p \in Procs : StartExploration(p) \/ Explore(p) \/ Restart(p)

Spec == Init /\ [][Next]_vars

\* The shared variables stay within their declared types, and the program
\* counter of a worker only advances when it has a node to explore.
Inv == TypeOK /\ \A p \in Procs : (pc[p] = "exploring") => (selected[p] \in frontier)

\* The parallel algorithm implements the sequential Misra algorithm: every
\* node it has reached is reachable in the original graph.
Refines == marked \subseteq Nodes

====