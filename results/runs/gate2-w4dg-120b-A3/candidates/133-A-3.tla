---- MODULE MCParReach ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS Nodes, Root, Procs, Succ

VARIABLES marked, frontier, pc, pick, succs

vars == <<marked, frontier, pc, pick, succs>>

TypeOK ==
  /\ marked \subseteq Nodes
  /\ frontier \in Seq(Nodes)
  /\ pc \in [Procs -> {"idle", "pick", "expand", "done"}]
  /\ pick \in [Procs -> Nodes \cup {"none"}]
  /\ succs \in [Procs -> SUBSET Nodes]

Init ==
  /\ marked = {Root}
  /\ frontier = <<Root>>
  /\ pc = [p \in Procs |-> "idle"]
  /\ pick = [p \in Procs |-> "none"]
  /\ succs = [p \in Procs |-> {}]

Take(p, n) ==
  /\ pc[p] = "idle"
  /\ n \in DOMAIN frontier
  /\ pick' = [pick EXCEPT ![p] = frontier[n]]
  /\ pc' = [pc EXCEPT ![p] = "pick"]
  /\ frontier' = SeqSubSeq(frontier, 1, n - 1) \o SeqSubSeq(frontier, n + 1, Len(frontier))
  /\ UNCHANGED <<marked, succs>>

Expand(p) ==
  /\ pc[p] = "pick"
  /\ succs' = [succs EXCEPT ![p] = ConnectedToSomeButNotAll(pick[p])]
  /\ pc' = [pc EXCEPT ![p] = "expand"]
  /\ UNCHANGED <<marked, frontier, pick>>

Mark(p, n) ==
  /\ pc[p] = "expand"
  /\ n \in succs[p]
  /\ n \notin marked
  /\ Len(frontier) < Cardinality(Nodes)
  /\ marked' = marked \cup {n}
  /\ frontier' = Append(frontier, n)
  /\ succs' = [succs EXCEPT ![p] = succs[p] \ {n}]
  /\ pc' = [pc EXCEPT ![p] = IF succs[p] \ {n} = {} THEN "done" ELSE "expand"]
  /\ UNCHANGED pick

Done(p) ==
  /\ pc[p] = "expand"
  /\ succs[p] = {}
  /\ pc' = [pc EXCEPT ![p] = "done"]
  /\ UNCHANGED <<marked, frontier, pick, succs>>

Next ==
  \/ \E p \in Procs, n \in 1 .. Len(frontier): Take(p, n)
  \/ \E p \in Procs: Expand(p)
  \/ \E p \in Procs, n \in Nodes: Mark(p, n)
  \/ \E p \in Procs: Done(p)

Spec == Init /\ [][Next]_vars

Inv == TypeOK

Refines == TRUE

LimitedSeq == Sequences!Seq
ConnectedToSomeButNotAll == Succ

====