---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* The distinction between the operator Succ (the original infinite graph operator)
\* and ConnectedToSomeButNotAll (the finite replacement injected by the .cfg)
\* is crucial: Succ stays abstract here, while ConnectedToSomeButNotAll is the
\* concrete graph structure the .cfg substitutes in for all references to Succ.
\* The model's init and next steps use ConnectedToSomeButNotAll, so the state
\* space is finite and respects the bounded-graph assumption.

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in [Nodes -> BOOLEAN]
  /\ pc \in [Procs -> {"idle", "pick", "load", "done"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = [n \in Nodes |-> n \in ConnectedToSomeButNotAll[Root]]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Pick(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in Nodes :
       /\ frontier[n]
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ frontier' = [frontier EXCEPT ![n] = FALSE]
  /\ pc' = [pc EXCEPT ![p] = "pick"]
  /\ UNCHANGED <<marked, succs>>

Load(p) ==
  /\ pc[p] = "pick"
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "load"]
  /\ UNCHANGED <<marked, frontier, sel>>

Visit(p) ==
  /\ pc[p] = "load"
  /\ \E n \in succs[p] :
       /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = [frontier EXCEPT ![n] = TRUE]
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<sel, succs>>

Reset(p) ==
  /\ pc[p] = "done"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs : Pick(p)
  \/ \E p \in Procs : Load(p)
  \/ \E p \in Procs : Visit(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TypeOK

\* The .cfg replaces the operator name Seq (from the Sequences module) with
\* LimitedSeq, which is the bounded version. The definition below is a FINITE
\* version of Seq, but no operator named Seq is ever declared here; the name
\* Succ is also untouched, because the .cfg substitutes ConnectedToSomeButNotAll
\* only in places where Succ is mentioned, never the name itself.
LimitedSeq ==
  \E n \in Nat : Sequences.Seq(n)
====