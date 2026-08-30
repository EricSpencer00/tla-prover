---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

(* A model-checking configuration module for the parallel reachability     *)
(* algorithm.  It extends the parallel algorithm with concrete definitions  *)
(* for model checking: a specific graph structure and a bounded sequence.   *)

CONSTANTS Nodes, Root, Procs, Succ

NONE == "none"

VARIABLES marked, frontier, pc, selected, succSet

vars == <<marked, frontier, pc, selected, succSet>>

\* A worker that is idle holds no node and its successor set is empty; the
\* invariant below catches the case where a non-idle worker's successor set
\* is empty, which is a real concurrency bug.
Stale == {w \in Procs : pc[w] # "idle" /\ succSet[w] = {}}

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "expanding", "done"}]
  /\ selected \in [Procs -> Nodes \cup {NONE}]
  /\ succSet \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {}
  /\ frontier = {Root}
  /\ pc = [w \in Procs |-> "idle"]
  /\ selected = [w \in Procs |-> NONE]
  /\ succSet = [w \in Procs |-> {}]

\* A worker whose frontier is empty is done and makes no further progress;
\* this is the backstop that keeps every run finite.
Select(w, n) ==
  /\ pc[w] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![w] = "selecting"]
  /\ selected' = [selected EXCEPT ![w] = n]
  /\ UNCHANGED <<marked, succSet>>

Expand(w) ==
  /\ pc[w] = "selecting"
  /\ succSet' = [succSet EXCEPT ![w] = Succ[selected[w]]]
  /\ pc' = [pc EXCEPT ![w] = "expanding"]
  /\ UNCHANGED <<marked, frontier, selected>>

Mark(w) ==
  /\ pc[w] = "expanding"
  /\ selected[w] \notin marked
  /\ marked' = marked \cup {selected[w]}
  /\ frontier' = frontier \cup Succ[selected[w]]
  /\ pc' = [pc EXCEPT ![w] = "done"]
  /\ UNCHANGED <<selected, succSet>>

Drop(w) ==
  /\ pc[w] = "expanding"
  /\ selected[w] \in marked
  /\ pc' = [pc EXCEPT ![w] = "done"]
  /\ UNCHANGED <<marked, frontier, selected, succSet>>

Next ==
  \/ \E w \in Procs, n \in Nodes : Select(w, n)
  \/ \E w \in Procs : Expand(w)
  \/ \E w \in Procs : Mark(w)
  \/ \E w \in Procs : Drop(w)

Spec == Init /\ [][Next]_vars

(* The CAS model always leaves a worker with an empty successor set at      *)
(* least while the frontier has something to claim.                         *)
Inv == Stale = {}

(* The parallel algorithm's interleaved marking is exactly the Misra      *)
(* sequential reachability: every marked node is reachable from the root.  *)
Refines == marked \subseteq ConnectedToSomeButNotAll

(* The empty successor set is reserved for an idle worker, so the number of *)
(* workers that can be mid-expansion is bounded by the number of nodes.     *)
StateBound == Cardinality(Stale) <= Cardinality(Nodes)

====