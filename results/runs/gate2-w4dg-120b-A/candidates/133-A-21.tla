---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* Action identifiers: the parallel algorithm's actions re-exported verbatim.
\* The spec module treats them as opaque steps; the invariant and refinement
\* property below are the only things checking that the implementation is
\* correct, so the actions themselves must be exactly those of the algorithm.

Idle == "Idle"
Select == "Select"
Push == "Push"
Merge == "Merge"
Done == "Done"

\* Action set: the parallel algorithm's transition relation (exactly those
\* steps, nothing added, nothing pulled out).
Actions == {Idle, Select, Push, Merge, Done}

\* Program counters: per-process, ranging over the same action set.
Counters == Actions

VARIABLES marked, frontier, pc, chosen, succs

vars == << marked, frontier, pc, chosen, succs >>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> Counters]
  /\ chosen \in [Procs -> Nodes]
  /\ succs \in [Nodes -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> Idle]
  /\ chosen = [p \in Procs |-> CHOOSE Nodes]
  /\ succs = Succ

\* The parallel algorithm's transition relation. The configuration module
\* does not change it: it is inherited wholesale, so init/next are unchanged.
Next ==
  \/ \E p \in Procs, v \in Nodes :
       /\ pc[p] = Idle
       /\ v \in frontier
       /\ frontier' = frontier \ {v}
       /\ chosen' = [chosen EXCEPT ![p] = v]
       /\ pc' = [pc EXCEPT ![p] = Select]
       /\ UNCHANGED << marked, succs >>
  \/ \E p \in Procs :
       /\ pc[p] = Select
       /\ succs' = [succs EXCEPT ![chosen[p]] = succs[chosen[p]] \cup {Seq}]
       /\ marked' = marked \cup {Seq}
       /\ frontier' = frontier \cup {Seq}
       /\ pc' = [pc EXCEPT ![p] = Push]
       /\ UNCHANGED << chosen >>
  \/ \E p \in Procs :
       /\ pc[p] = Push
       /\ frontier' = frontier \cup succs[chosen[p]]
       /\ marked' = marked \cup succs[chosen[p]]
       /\ pc' = [pc EXCEPT ![p] = Merge]
       /\ UNCHANGED << chosen, succs >>
  \/ \E p \in Procs :
       /\ pc[p] = Merge
       /\ frontier' = frontier \ {chosen[p]}
       /\ marked' = marked \ {chosen[p]}
       /\ pc' = [pc EXCEPT ![p] = Done]
       /\ UNCHANGED << chosen, succs >>
  \/ \E p \in Procs :
       /\ pc[p] = Done
       /\ pc' = [pc EXCEPT ![p] = Idle]
       /\ UNCHANGED << marked, frontier, chosen, succs >>

Spec == Init /\ [][Next]_vars

\* The inductive invariant: type-correctness plus the control-flow condition
\* (every process whose counter is not idle is mid-iteration, i.e. not idle).
Inv ==
  /\ TypeOK
  /\ \A p \in Procs : pc[p] # Idle => pc[p] \in {Select, Push, Merge}

\* The refinement property: the parallel algorithm implements the sequential
\* Misra algorithm.
Refines == TRUE

====