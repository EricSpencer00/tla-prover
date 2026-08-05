---- MODULE MCParReach ----
EXTENDS Integers, Sequences, FiniteSets

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, sel, suc

vars == <<marked, frontier, pc, sel, suc>>

Active == {p \in Procs : \E i \in DOMAIN frontier : frontier[i] = p}
SeqLen == IF \E i \in DOMAIN frontier : i > 0 THEN Cardinality(DOMAIN frontier) - 1 ELSE 0

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(2)
  /\ pc \in [Procs -> {"idle", "pick", "explore"}]
  /\ sel \in [Procs -> Nodes \cup {"none"}]
  /\ suc \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = <<>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ sel = [p \in Procs |-> "none"]
  /\ suc = [p \in Procs |-> {}]

Pick(p, n) ==
  /\ pc[p] = "idle"
  /\ frontier' = Append(frontier, p)
  /\ pc' = [pc EXCEPT ![p] = "pick"]
  /\ sel' = [sel EXCEPT ![p] = n]
  /\ suc' = [suc EXCEPT ![p] = {}]
  /\ UNCHANGED marked

Explore(p) ==
  /\ pc[p] = "pick"
  /\ suc' = [suc EXCEPT ![p] = Succ[sel[p]]]
  /\ pc' = [pc EXCEPT ![p] = "explore"]
  /\ UNCHANGED <<marked, frontier, sel>>

Mark(p, m) ==
  /\ pc[p] = "explore"
  /\ m \in suc[p]
  /\ m \notin marked
  /\ marked' = marked \cup {m}
  /\ frontier' = SubSeq(frontier, 1, SeqLen)
  /\ pc' = [pc EXCEPT ![p] = "idle"]
  /\ sel' = [sel EXCEPT ![p] = "none"]
  /\ suc' = [suc EXCEPT ![p] = {}]

Next ==
  \/ \E p \in Procs, n \in Nodes : Pick(p, n)
  \/ \E p \in Procs : Explore(p)
  \/ \E p \in Procs, m \in Nodes : Mark(p, m)

Spec == Init /\ [][Next]_vars

Inv == TypeOK /\ UNCHANGED <<>>

Refines == TRUE

ASSUME ConnectedToSomeButNotAll == Succ
ASSUME LimitedSeq == Seq

====