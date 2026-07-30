---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ
vars == <<marked, frontier, pc, sel, succ>>

Init ==
  /\ marked = {[n \in Nodes |-> FALSE]}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ succ = [n \in Nodes |-> Succ[n]]

Take(n, p) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED <<marked, succ>>

Put(p) ==
  /\ pc[p] = "working"
  /\ sel[p] # "none"
  /\ marked' = [marked EXCEPT ![sel[p]] = TRUE]
  /\ frontier' = frontier \cup succ[sel[p]]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<succ>>

Next ==
  \/ \E n \in Nodes, p \in Procs : Take(n, p)
  \/ \E p \in Procs : Put(p)

Spec == Init /\ [][Next]_vars

MarkedCount == Cardinality({n \in Nodes : marked[n]})

Inv ==
  /\ frontier \subseteq Nodes
  /\ \A n \in Nodes : marked[n] => frontier[n] = FALSE
  /\ \A p \in Procs : pc[p] \in {"idle", "working"}

Refines == MarkedCount <= Cardinality(Nodes)

ConnectedToSomeButNotAll(n) ==
  \E m \in Nodes :
    /\ m # n
    /\ m \in succ[n]
    /\ Cardinality(succ[n]) >= 2

LimitedSeq ==
  [n \in Nodes |-> IF n \in Nodes /\ n = Root THEN <<>> ELSE <<n>>]

====