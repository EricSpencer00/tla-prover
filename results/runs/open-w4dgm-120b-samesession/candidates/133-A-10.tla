---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs

Vars == <<marked, frontier, pc, selected, succs>>

RangeOf(s) == {s[i] : i \in 1..Len(s)}

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [n \in Nodes |-> Succ(n)]

Select(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ pc' = [pc EXCEPT ![p] = "active"]
  /\ selected' = [selected EXCEPT ![p] = n]
  /\ succs' = [succs EXCEPT ![n] = Succ(n)]
  /\ UNCHANGED <<marked, frontier>>

MarkExplored(p) ==
  /\ pc[p] = "active"
  /\ selected[p] \in frontier
  /\ frontier' = frontier \ {selected[p]}
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, selected, succs>>

MarkNew(p) ==
  /\ pc[p] = "active"
  /\ selected[p] \in frontier
  /\ frontier' = frontier \ {selected[p]}
  /\ marked' = marked \cup {selected[p]}
  /\ frontier' = frontier \cup succs[selected[p]]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<selected, succs>>

DropBad(p) ==
  /\ pc[p] = "active"
  /\ selected[p] \notin frontier
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ UNCHANGED <<marked, frontier, selected, succs>>

Next ==
  \/ \E p \in Procs, n \in Nodes : Select(p, n)
  \/ \E p \in Procs : MarkExplored(p)
  \/ \E p \in Procs : MarkNew(p)
  \/ \E p \in Procs : DropBad(p)

Spec ==
  /\ Init
  /\ [][Next]_Vars
  /\ \A p \in Procs : WF_Vars(MarkExplored(p))
  /\ \A p \in Procs : WF_Vars(MarkNew(p))
  /\ \A p \in Procs : WF_Vars(DropBad(p))

ValuesFit ==
  /\ selected["p1"] \in Nodes \cup {"none"}
  /\ selected["p2"] \in Nodes \cup {"none"}
  /\ \/ pc["p1"] \in {"idle", "active"}
     \/ pc["p2"] \in {"idle", "active"}
  /\ frontier \subseteq Nodes
  /\ marked \subseteq Nodes
  /\ succs \in [Nodes -> SUBSET Nodes]

Refines ==
  \A n \in Nodes : (n \in frontier) ~> (n \in marked)

Inv == ValuesFit

LimitedSeq == Seq

====