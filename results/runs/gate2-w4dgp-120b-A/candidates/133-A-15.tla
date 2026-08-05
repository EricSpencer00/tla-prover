---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

\* ConnectedToSomeButNotAll is a sequencing-friendly version of Succ: at every node
\* there is at least one outgoing edge, but never the full set of nodes, which
\* keeps the graph finite and the reachable state space small.
ConnectedToSomeButNotAll == Nodes \ {Root}

VARIABLES marked, frontier, pc, selection, succs

vars == <<marked, frontier, pc, selection, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ selection \in [Procs -> Seq({Nodes})]
  /\ succs \in [Nodes -> SUBSET ConnectedToSomeButNotAll]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selection = [p \in Procs |-> <<>>]
  /\ succs = [n \in Nodes |-> ConnectedToSomeButNotAll]

InitStep(p) ==
  /\ pc[p] = "idle"
  /\ \E n \in frontier : succs[n] # {}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ selection' = [selection EXCEPT ![p] = <<>>]
  /\ UNCHANGED <<marked, frontier, succs>>

Step(p, n) ==
  /\ pc[p] = "working"
  /\ n \in succs[Head(selection[p])]
  /\ selection' = [selection EXCEPT ![p] = Tail(selection[p])]
  /\ UNCHANGED <<marked, frontier, pc, succs>>

Seek(p, n) ==
  /\ pc[p] \in {"idle", "working"}
  /\ Len(selection[p]) < Cardinality(Nodes)
  /\ selection' = [selection EXCEPT ![p] = Append(selection[p], n)]
  /\ UNCHANGED <<marked, frontier, pc, succs>>

Mark(p) ==
  /\ pc[p] = "working"
  /\ selection[p] # <<>>
  /\ Head(selection[p]) \notin marked
  /\ marked' = marked \cup {Head(selection[p])}
  /\ frontier' = frontier \cup {Head(selection[p])}
  /\ UNCHANGED <<pc, selection, succs>>

Finish(p) ==
  /\ pc[p] = "working"
  /\ selection[p] = <<>>
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, selection, succs>>

Next ==
  \/ \E p \in Procs : InitStep(p) \/ Mark(p) \/ Finish(p)
  \/ \E p \in Procs, n \in Nodes : Seek(p, n) \/ Step(p, n)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == \A p \in Procs : p \notin Procs

====