---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

ASSUME /\ Cardinality(Nodes) = 4
       /\ Cardinality(Succ) = 2

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> 0..2]
  /\ sel \in [Procs -> 0..4]
  /\ succs \subseteq [pro : Procs, v : Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> 0]
  /\ sel = [p \in Procs |-> 0]
  /\ succs = {}

Select(p, v) ==
  /\ v \in frontier
  /\ frontier' = frontier \ {v}
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ sel' = [sel EXCEPT ![p] = v]
  /\ UNCHANGED <<marked, succs>>

Visit(p, w) ==
  /\ pc[p] = 1
  /\ w \in Succ
  /\ succs' = succs \cup {[pro |-> p, v |-> w]}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED <<marked, frontier, sel>>

Explore(p, w) ==
  /\ pc[p] = 2
  /\ w \notin marked
  /\ marked' = marked \cup {w}
  /\ frontier' = frontier \cup {w}
  /\ pc' = [pc EXCEPT ![p] = 0]
  /\ UNCHANGED <<sel, succs>>

Next ==
  \/ \E p \in Procs, v \in Nodes : Select(p, v)
  \/ \E p \in Procs, w \in Nodes : Visit(p, w)
  \/ \E p \in Procs, w \in Nodes : Explore(p, w)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == Inv

====