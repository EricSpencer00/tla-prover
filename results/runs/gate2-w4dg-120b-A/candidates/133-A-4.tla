---- MODULE MCParReach ----
EXTENDS Naturals

CONSTANTS Nodes, Root, Procs, Succ, Seq

\* The shared marked set and frontier are the two views of the same collection;
\* the invariant ties them together.
VARIABLES marked, frontier, pc, sel, succset, seq

vars == <<marked, frontier, pc, sel, succset, seq>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "active", "done"}]
  /\ sel \in [Procs -> Nodes]
  /\ succset \in [Procs -> SUBSET Nodes]
  /\ seq \in Seq

ControlFlowOK ==
  /\ marked # {}
  /\ frontier = marked
  /\ \A q \in Procs : pc[q] = "done" => frontier = {}
  /\ \A p \in Procs : pc[p] = "active" => sel[p] \in marked

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [q \in Procs |-> "idle"]
  /\ sel = [q \in Procs |-> CHOOSE n \in Nodes : TRUE]
  /\ succset = [q \in Procs |-> {}]
  /\ seq = {}

Begin(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ succset' = [succset EXCEPT ![p] = Succ[n]]
       /\ frontier' = frontier \ {n}
       /\ marked' = marked \cup {n}
  /\ pc' = [pc EXCEPT ![p] = "active"]
  /\ seq' = seq \cup {n}

Select(p) ==
  /\ pc[p] = "active"
  /\ \E n \in succset[p] : n \notin marked
       /\ sel' = [sel EXCEPT ![p] = n]
       /\ succset' = [succset EXCEPT ![p] = Succ[n]]
       /\ marked' = marked \cup {n}
  /\ seq' = seq \cup {n}

Done(p) ==
  /\ pc[p] = "active"
  /\ \A n \in succset[p] : n \in marked
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, sel, succset, seq>>

Next ==
  \/ \E p \in Procs : Begin(p)
  \/ \E p \in Procs : Select(p)
  \/ \E p \in Procs : Done(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ ControlFlowOK

Refines == Inv

====