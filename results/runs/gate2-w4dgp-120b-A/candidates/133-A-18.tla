---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES markedSet, frontier, pc, selected, succs
vars == <<markedSet, frontier, pc, selected, succs>>

Init ==
  /\ markedSet = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> [n \in Nodes |-> FALSE]]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "busy"]
  /\ selected' = [selected EXCEPT ![p] = [i \in Nodes |-> i = n]]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<markedSet, frontier>>

Visit(p) ==
  /\ pc[p] = "busy"
  /\ Len(succs[p]) < Cardinality(Nodes)
  /\ \E m \in Succ[n] : succs' = [succs EXCEPT ![p] = Append(succs[p], m)]
  /\ UNCHANGED <<markedSet, frontier, pc, selected>>

Commit(p) ==
  /\ pc[p] = "busy"
  /\ \E m \in Succ[n] : m \notin markedSet
  /\ markedSet' = markedSet \cup {m}
  /\ frontier' = frontier \cup {m}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = [i \in Nodes |-> FALSE]]
  /\ succs' = [succs EXCEPT ![p] = << >>]

Finish(p) ==
  /\ pc[p] = "busy"
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ selected' = [selected EXCEPT ![p] = [i \in Nodes |-> FALSE]]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED <<markedSet, frontier>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Visit(p)
  \/ \E p \in Procs : Commit(p)
  \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A p \in Procs :
       /\ pc[p] \in {"idle", "busy"}
       /\ Cardinality(succs[p]) <= Cardinality(Nodes)
  /\ markedSet \subseteq Nodes
  /\ frontier \subseteq Nodes

ConnectedToSomeButNotAll(n) == \E m \in Succ[n] : m \in markedSet
Refines == ConnectedToSomeNotAll
====