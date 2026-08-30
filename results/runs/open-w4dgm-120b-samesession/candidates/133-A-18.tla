---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs

None == "none"
NoNode == "empty"

ASSUME Root \in Nodes

VARIABLES marked, frontier, pc, sel, succs

vars == <<marked, frontier, pc, sel, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "selecting", "collecting"}]
  /\ sel \in [Procs -> {NoNode} \cup Nodes]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = {Root}
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> NoNode]
  /\ succs = [p \in Procs |-> {}]

BeginSelect(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in frontier
  /\ frontier' = frontier \ {n}
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ pc' = [pc EXCEPT ![p] = "selecting"]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED marked

BeginCollect(p) ==
  /\ pc[p] = "selecting"
  /\ succs' = [succs EXCEPT ![p] = {None}]
  /\ pc' = [pc EXCEPT ![p] = "collecting"]
  /\ UNCHANGED <<marked, frontier, sel>>

AddSuccessor(p, m) ==
  /\ pc[p] = "collecting"
  /\ succs' = IF m \in succs[p]
        THEN succs
        ELSE [succs EXCEPT ![p] = succs[p] \cup {m}]
  /\ UNCHANGED <<marked, frontier, pc, sel>>

Commit(p) ==
  /\ pc[p] = "collecting"
  /\ NoNode \in succs[p]
  /\ marked' = marked \cup succs[p]
  /\ frontier' = frontier \cup succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = NoNode]
  /\ succs' = [succs EXCEPT ![p] = {}]

Abandon(p) ==
  /\ pc[p] = "collecting"
  /\ NoNode \notin succs[p]
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = NoNode]
  /\ succs' = [succs EXCEPT ![p] = {}]
  /\ UNCHANGED <<marked, frontier>>

Done ==
  /\ frontier = {}
  /\ \A p \in Procs : pc[p] = "idle"
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Procs, n \in Nodes : BeginSelect(p, n)
  \/ \E p \in Procs : BeginCollect(p)
  \/ \E p \in Procs, m \in Nodes : AddSuccessor(p, m)
  \/ \E p \in Procs : Commit(p)
  \/ \E p \in Procs : Abandon(p)
  \/ Done

Spec == Init /\ [][Next]_vars

Inv ==
  /\ marked \cap frontier = {}
  /\ marked \cup frontier = Nodes
  /\ \A p \in Procs :
       pc[p] = "collecting" => (sel[p] \in Nodes /\ NoNode \in succs[p])
  /\ \A p \in Procs : pc[p] \in {"idle", "selecting", "collecting"}

Refines ==
  \A p \in Procs :
    /\ (pc[p] = "selecting") => (sel[p] \in frontier)
    /\ (pc[p] = "collecting") => (sel[p] \in marked)

Rewrite ==
  /\ Succ = ConnectedToSomeButNotAll
  /\ Seq = LimitedSeq

====