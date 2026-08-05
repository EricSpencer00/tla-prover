---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences, MCSeq

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, selected, succs
vars == <<marked, frontier, pc, selected, succs>>

TypeInv ==
  /\ marked \subseteq Nodes
  /\ frontier \subseteq Nodes
  /\ pc \in [Procs -> {"idle", "working", "done"}]
  /\ selected \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> Seq(Nodes)]

Init ==
  /\ marked = {Root}
  /\ frontier = {}
  /\ pc = [p \in Procs |-> "idle"]
  /\ selected = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> << >>]

SetFrontier ==
  /\ frontier = {}
  /\ frontier' = Succ[Root]
  /\ UNCHANGED <<marked, pc, selected, succs>>

Pick(p) ==
  /\ pc[p] = "idle"
  /\ frontier \neq {}
  /\ selected' = [selected EXCEPT ![p] = CHOOSE v \in frontier : TRUE]
  /\ frontier' = frontier \ {selected[p]}
  /\ succs' = [succs EXCEPT ![p] = << >>]
  /\ pc' = [pc EXCEPT ![p] = "working"]
  /\ UNCHANGED marked

ProcessSucc(p, i) ==
  /\ pc[p] = "working"
  /\ i <= Len(succs[p])
  /\ marked' = marked \cup {succs[p][i]}
  /\ UNCHANGED <<frontier, pc, selected, succs>>

Finish(p) ==
  /\ pc[p] = "working"
  /\ Len(succs[p]) = 0
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ selected' = [selected EXCEPT ![p] = "none"]
  /\ UNCHANGED <<marked, frontier, succs>>

Next ==
  \/ SetFrontier
  \/ \E p \in Procs : Pick(p)
  \/ \E p \in Procs : \E i \in 1..Len(succs[p]) : ProcessSucc(p, i)
  \/ \E p \in Procs : Finish(p)

Spec == Init /\ [][Next]_vars

Inv == TypeInv

Refines == \A p \in Procs : pc[p] = "done" => selected[p] = "none"

Succ2 == {<<1, 2>>, <<1, 3>>, <<2, 3>>, <<2, 1>>, <<3, 1>>, <<3, 2>>}
ConnectedToSomeButNotAll == Succ2
LimitedSeq == LimitedSeq

====