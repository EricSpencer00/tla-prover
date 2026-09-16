---- MODULE W4Od3m3p0t2 ----
\* A bank's interbank settlement batch is driven by a single elected leader among two nodes that share
\* one settlement pool, with leader election and failover across terms. Starting a new term clears the
\* leader and every vote. Each node casts one vote per term; a node is elected leader only once both
\* nodes have voted for it, giving it the whole quorum. The leader advances the settlement batch. On
\* failover the leader crashes and is cleared, and stalled votes may be cleared to retry. Whenever a
\* leader stands, every node's current vote names that leader, so at most one node ever leads a term.
EXTENDS Naturals

NONE == "none"
Nodes == {"n1", "n2"}
MaxTerm == 2
MaxBatch == 2

VARIABLES term, leader, votedFor, batch

TypeOK ==
  /\ term \in 0..MaxTerm
  /\ leader \in Nodes \cup {NONE}
  /\ votedFor \in [Nodes -> Nodes \cup {NONE}]
  /\ batch \in 0..MaxBatch

Init ==
  /\ term = 0
  /\ leader = NONE
  /\ votedFor = [n \in Nodes |-> NONE]
  /\ batch = 0

StartTerm ==
  /\ term < MaxTerm
  /\ term' = term + 1
  /\ leader' = NONE
  /\ votedFor' = [n \in Nodes |-> NONE]
  /\ UNCHANGED batch

Vote(n, cand) ==
  /\ votedFor[n] = NONE
  /\ leader = NONE
  /\ votedFor' = [votedFor EXCEPT ![n] = cand]
  /\ UNCHANGED <<term, leader, batch>>

Elect(cand) ==
  /\ leader = NONE
  /\ \A n \in Nodes : votedFor[n] = cand
  /\ leader' = cand
  /\ UNCHANGED <<term, votedFor, batch>>

Settle(n) ==
  /\ leader = n
  /\ batch < MaxBatch
  /\ batch' = batch + 1
  /\ UNCHANGED <<term, leader, votedFor>>

Crash(n) ==
  /\ leader = n
  /\ leader' = NONE
  /\ UNCHANGED <<term, votedFor, batch>>

ClearVotes ==
  /\ leader = NONE
  /\ \E n \in Nodes : votedFor[n] # NONE
  /\ votedFor' = [n \in Nodes |-> NONE]
  /\ UNCHANGED <<term, leader, batch>>

Next ==
  \/ StartTerm
  \/ \E n \in Nodes, cand \in Nodes : Vote(n, cand)
  \/ \E cand \in Nodes : Elect(cand)
  \/ \E n \in Nodes : Settle(n)
  \/ \E n \in Nodes : Crash(n)
  \/ ClearVotes

Spec == Init /\ [][Next]_<<term, leader, votedFor, batch>>

LeaderBacked ==
  leader # NONE => \A n \in Nodes : votedFor[n] = leader
====