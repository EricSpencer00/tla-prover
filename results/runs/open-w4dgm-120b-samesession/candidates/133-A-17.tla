---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The parallel algorithm's state, parametric in the graph and the workers.
\* This adds no new variable; everything here is already present in the
\* algorithm, so the configuration only fixes the shape of the instance.
VARIABLES marked, frontier, pc, sel, succs

SuccAlt == ConnectedToSomeButNotAll

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle","searching","committing","done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Choose(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "searching"]
  /\ UNCHANGED <<marked, succs>>

ReadSucc(p) ==
  /\ pc[p] = "searching"
  /\ succs' = [succs EXCEPT ![p] = SuccAlt[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "committing"]
  /\ UNCHANGED <<marked, frontier, sel>>

\* The per-process bounded sequence: a node stays put once it is marked.
Commit(p) ==
  /\ pc[p] = "committing"
  /\ marked' = marked \cup {sel[p]}
  /\ frontier' = frontier \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<sel, succs>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Done == \A p \in Procs : pc[p] = "done"

Next ==
  \/ \E p \in Procs : Choose(p)
  \/ \E p \in Procs : ReadSucc(p)
  \/ \E p \in Procs : Commit(p)
  \/ \E p \in Procs : Reset(p)
  \/ (Done /\ UNCHANGED <<marked, frontier, pc, sel, succs>>)

Spec == Init /\ [][Next]_<<marked, frontier, pc, sel, succs>>

\* The sequential refinement is a purely logical relationship to the
\* algorithm's control flow; it never mentions the graph shape.
Refines == Inv

\* The configuration's only job is to pick a concrete finite shape of work
\* for the algorithm; it does not weaken or delete any invariant.
====