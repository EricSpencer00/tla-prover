---- MODULE MCParReach ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succ = Succ

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ Len(frontier) > 0
  /\ Head(frontier) = n
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ frontier' = Tail(frontier)
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<marked, succ>>

Explore(p, m) ==
  /\ pc[p] = "working"
  /\ m \in succ[sel[p]]
  /\ m \notin marked
  /\ marked' = marked \cup {m}
  /\ frontier' = Append(frontier, m)
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ UNCHANGED succ

StayIdle(p) ==
  /\ pc[p] = "idle"
  /\ Len(frontier) = 0
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs, m \in Nodes : Explore(p, m)
  \/ \E p \in Procs : StayIdle(p)

Spec == Init /\ [][Next]_vars

Inv ==
  /\ \A p \in Procs : pc[p] \in {"idle", "working"}
  /\ \A p \in Procs : sel[p] \in Nodes \cup {"none"}
  /\ \A p \in Procs, n \in Nodes : sel[p] = n => n \in frontier

Refines == Inv

CONSTANT Succ == ConnectedToSomeButNotAll

Succ == ConnectedToSomeButNotAll

LimitedSeq == Seq

====