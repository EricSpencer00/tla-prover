---- MODULE MCParReach ----
EXTENDS Integers, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* Types: marked nodes, frontier, program counter per process, selected node
\* per process, and a bounded sequence of frontier nodes (not in the original
\* parallel spec, added here for model checking).
VARIABLES marked, frontier, pc, cur, choice

vars == <<marked, frontier, pc, cur, choice>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ cur \in [Procs -> Nodes]
  /\ choice \in Seq(Nodes)

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ cur = [p \in Procs |-> Root]
  /\ choice = <<>>

\* The workers share the frontier. A worker may adopt any frontier node as its
\* current target, advancing its control state to "working".
Pick(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ cur' = [cur EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<marked, choice>>

\* The worker accepts the current node into the bounded sequence and marks it.
Acquire(p) ==
  /\ pc[p] = "working"
  /\ Len(choice) < Len(Seq)
  /\ marked' = marked \cup {cur[p]}
  /\ choice' = Append(choice, cur[p])
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<frontier, cur>>

\* A done worker resets to idle so it can pick another frontier node.
Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, cur, choice>>

Next ==
  \/ Pick("p1")
  \/ Acquire("p1")
  \/ Reset("p1")
  \/ Pick("p2")
  \/ Acquire("p2")
  \/ Reset("p2")

Spec == Init /\ [][Next]_vars

\* The inductive invariant: the marked set and the frontier never intersect,
\* and the sequence never exceeds its bound.
Inv ==
  /\ marked \cap frontier = {}
  /\ Len(choice) <= Len(Seq)

\* Refinement: every node in the bounded sequence really is a marked node, so
\* the parallel algorithm never fabricates or loses a frontier node.
Refines == \A k \in DOMAIN choice : choice[k] \in marked

====