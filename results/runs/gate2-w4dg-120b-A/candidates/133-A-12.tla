---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ, Seq

VARIABLES marked, frontier, pc, pick, succs

vars == <<marked, frontier, pc, pick, succs>>

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ pick = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> Seq]

Explore(p) ==
  /\ pc[p] = "idle"
  /\ frontier # {}
  /\ \E n \in frontier :
       /\ pick' = [pick EXCEPT ![p] = n]
       /\ frontier' = frontier \ {n}
  /\ pc' = [pc EXCEPT ![p] = "picking"]
  /\ succs' = [succs EXCEPT ![p] = Seq]
  /\ UNCHANGED marked

Fetch(p) ==
  /\ pc[p] = "picking"
  /\ succs[p] # << >>
  /\ LET m == Head(succs[p]) IN
       /\ succs' = [succs EXCEPT ![p] = Tail(succs[p])]
       /\ IF m \in marked
            THEN UNCHANGED <<marked, frontier>>
            ELSE marked' = marked \cup {m} /\ frontier' = frontier \cup {m}
  /\ UNCHANGED <<pc, pick>>

Finish(p) ==
  /\ pc[p] \in {"picking"}
  /\ succs[p] = Seq
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ pick' = [pick EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succs>>

Next ==
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs : Fetch(p)
  \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

MarkBound == Cardinality(marked) <= Cardinality(Nodes)

ControlFlow ==
  /\ \A p \in Procs : pc[p] \in {"idle", "picking"}
  /\ \A p \in Procs : pc[p] = "idle" => pick[p] = "none"

Inv == MarkBound /\ ControlFlow

Refines ==
  /\ \A p \in Procs : pc[p] = "idle" => pick[p] = "none"
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes

====