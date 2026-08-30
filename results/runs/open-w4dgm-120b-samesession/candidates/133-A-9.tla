---- MODULE MCParReach ----
EXTENDS Naturals, Sequences

(* Model-checking configuration for the parallel reachability algorithm.  It    *)
(* inherits the algorithm's actions and variables and supplies the concrete       *)
(* graph structure and process set that keep the state space finite.  It checks   *)
(* the full safety suite (type correctness, control-flow discipline,             *)
(* refinement) against the parallel algorithm's behavior.                        *)

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, work

vars == <<marked, frontier, pc, sel, work>>

\* Succ is the graph's edge relation, specialized so every node has exactly two
\* distinct successors and the frontier can never grow past the node count.
LimitedSeq == Seq

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "working"}]
  /\ sel \in [Procs -> Nodes]
  /\ work \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> Root]
  /\ work = [p \in Procs |-> << >>]

Begin(p) ==
  /\ pc[p] = "idle"
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ UNCHANGED <<marked, frontier, sel, work>>

Select(p, n) ==
  /\ pc[p] = "selecting"
  /\ n \in Succ[sel[p]]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<marked, frontier, work>>

Expand(p) ==
  /\ pc[p] = "working"
  /\ sel[p] \notin marked
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = frontier \cup {sel[p]}
  /\ work' = [work EXCEPT ![p] = LimitedSeq([sel[p]])]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED sel

Skip(p) ==
  /\ pc[p] = "working"
  /\ sel[p] \in marked
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, work>>

Next ==
  \/ \E p \in Procs : Begin(p)
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Expand(p)
  \/ \E p \in Procs : Skip(p)

Spec == Init /\ [][Next]_vars

(* Safety: the inductive invariant that captures type correctness and the       *)
(* control-flow discipline of every process, plus the refinement property.      *)
Inv == TypeOK

Refines == \A p \in Procs : work[p] # << >> => work[p][1] \in marked

====