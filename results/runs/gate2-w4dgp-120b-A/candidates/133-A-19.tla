---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, succ

vars == <<marked, frontier, pc, sel, succ>>

Init ==
  /\ marked = {Root}
  /\ frontier = Succ[Root]
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> 0]
  /\ succ = [p \in Procs |-> << >>]

Claim ==
  \E p \in Procs :
    /\ pc[p] = "idle"
    /\ frontier # {}
    /\ marked' = marked \cup frontier
    /\ frontier' = {}
    /\ pc' = [pc EXCEPT ![p] = "working"]
    /\ sel' = [sel EXCEPT ![p] = 0]
    /\ succ' = [succ EXCEPT ![p] = << >>]

Explore ==
  \E p \in Procs :
    /\ pc[p] = "working"
    /\ sel[p] < Len(succ[p])
    /\ frontier' = frontier \cup Succ[succ[p][sel[p] + 1]]
    /\ sel' = [sel EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<marked, pc, succ>>

Expand ==
  \E p \in Procs :
    /\ pc[p] = "working"
    /\ sel[p] = Len(succ[p])
    /\ succ' = [succ EXCEPT ![p] = Succ[sel[p]]]
    /\ pc' = [pc EXCEPT ![p] = "idle"]
    /\ UNCHANGED <<marked, frontier, sel>>

Done ==
  /\ frontier = {}
  /\ \A p \in Procs : pc[p] = "idle"
  /\ UNCHANGED vars

Next == Claim \/ Explore \/ Expand \/ Done

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ \A p \in Procs : pc[p] \in {"idle", "working"}
  /\ \A p \in Procs : sel[p] \in 0..Cardinality(Nodes)
  /\ \A p \in Procs : succ[p] \in Seq(Nodes)

Refines == FrontierAlwaysSubset == frontier \subseteq Nodes

====