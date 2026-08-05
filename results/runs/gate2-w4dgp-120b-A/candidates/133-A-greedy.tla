---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> 0]
  /\ succs = [p \in Procs |-> << >>]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "selected"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ UNCHANGED marked

Explore(p) ==
  /\ pc[p] = "selected"
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ pc' = [pc EXCEPT ![p] = "exploring"]
  /\ UNCHANGED <<marked, frontier, sel>>

Append(p, n) ==
  /\ pc[p] = "exploring"
  /\ n \in Succ[sel[p]]
  /\ Len(succs[p]) < Cardinality(Nodes)
  /\ succs' = [succs EXCEPT ![p] = Append(succs[p], n)]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Mark(p) ==
  /\ pc[p] = "exploring"
  /\ succs[p] # << >>
  /\ LET n == Head(succs[p]) IN
       /\ n \notin marked
       /\ marked' = marked \cup {n}
       /\ frontier' = frontier \cup Succ[n]
  /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
  /\ UNCHANGED <<pc, sel>>

Done(p) ==
  /\ pc[p] \in {"selected", "exploring"}
  /\ succs[p] = << >>
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, sel, succs>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs, n \in Nodes : Append(p, n)
  \/ \E p \in Procs : Mark(p)
  \/ \E p \in Procs : Done(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in {"idle", "selected", "exploring"}
  /\ \A p \in Procs : pc[p] = "selected" => sel[p] \in frontier
  /\ \A p \in Procs : pc[p] = "exploring" => succs[p] # << >>

Refines == \A n \in Nodes : n \in marked

====