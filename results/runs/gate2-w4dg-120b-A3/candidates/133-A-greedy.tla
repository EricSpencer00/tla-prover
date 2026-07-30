---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "exploring"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ frontier' = frontier \ {n}
  /\ UNCHANGED <<marked, succs>>

Explore(p) ==
  /\ pc[p] = "selecting"
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<marked, frontier, sel>>

ExploreStep(p) ==
  /\ pc[p] = "exploring"
  /\ Len(succs[p]) < Cardinality(Nodes)
  /\ \E n \in Nodes :
       /\ n \notin marked
       /\ succs' = [succs EXCEPT ![p] = Append(@, n)]
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup {n}
  /\ UNCHANGED <<pc, sel>>

Finish(p) ==
  /\ pc[p] = "exploring"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<marked, frontier>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : ExploreStep(p)
  \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

ConnectedToSomeButNotAll(n) == \E m \in Nodes : m # n /\ m \in Succ

LimitedSeq == Seq

====