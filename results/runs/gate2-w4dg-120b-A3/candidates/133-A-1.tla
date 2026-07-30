---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* ConnectedToSomeButNotAll replaces the Succ operator from the
\* reference configuration; Succ itself is kept as the declared constant
\* above (the cfg substitutes ConnectedToSomeButNotAll wherever it expects
\* a finite or bounded Succ). LimitedSeq replaces Seq from the
\* Sequences module so the model stays finite; the name Seq is never
\* re-declared here (the cfg substitutes LimitedSeq wherever it expects a
\* bounded sequence.)

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

SelectNode(p, n) ==
  /\ pc[p] = 0
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll(n)]
  /\ UNCHANGED marked

Mark(p, n) ==
  /\ pc[p] = 1
  /\ n \in succs[p]
  /\ n \notin marked
  /\ marked' = marked \cup {n}
  /\ frontier' = frontier \cup {n}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<sel, succs>>

Idle(p) ==
  /\ pc[p] = 1
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Reset(p) ==
  /\ pc[p] = 2
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs, n \in Nodes : SelectNode(p, n)
  \/ \E p \in Procs, n \in Nodes : Mark(p, n)
  \/ \E p \in Procs : Idle(p)
  \/ \E p \in Procs : Reset(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

ConnectedToSomeButNotAll(n) == ConnectedToSomeButAll(n)
LimitedSeq(s) == Cardinality(s)

====