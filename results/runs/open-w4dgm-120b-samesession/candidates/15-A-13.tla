---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Control locations: one process per identity, no separate broadcaster.
VARIABLES correct, faulty, pc, rxMsgs, sentMsgs

vars == <<correct, faulty, pc, rxMsgs, sentMsgs>>

AllIds == 1..N
Senders == [snd : AllIds, t : {"ECHO"}]

InitBroadcastIds == {1, 2}
NonBroadcastIds == {3, 4}

InitSet == {InitBroadcastIds, NonBroadcastIds}

\* InitState is the corner case where no correct process ever broadcasts.
InitState == CHOOSE s \in InitSet : s = NonBroadcastIds

TypeOK ==
  /\ correct \subseteq AllIds
  /\ faulty \subseteq AllIds
  /\ pc \in [AllIds -> {"none", "rcvd", "sent", "accept"}]
  /\ rxMsgs \in [AllIds -> SUBSET Senders]
  /\ sentMsgs \subseteq Senders

Init ==
  /\ correct = {1, 2, 3}
  /\ faulty = {4}
  /\ pc = [i \in AllIds |-> IF i \in InitBroadcastIds THEN "rcvd" ELSE "none"]
  /\ rxMsgs = [i \in AllIds |-> {}]
  /\ sentMsgs = {}

\* A correct process may receive any new messages from correct and faulty senders.
Recv(p, msgs) ==
  /\ p \in correct
  /\ pc[p] # "accept"
  /\ msgs # {}
  /\ rxMsgs' = [rxMsgs EXCEPT ![p] = @ \cup msgs]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

MsgTypesFrom(p, q) ==
  {x \in rxMsgs[p] : x.snd = q}

\* Reception of the broadcaster's single INIT message is an immediate accept.
BroadcastAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "rcvd"
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sentMsgs' = sentMsgs \cup {[snd |-> p, t |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rxMsgs>>

\* Below N-T distinct ECHOs, a process sends ECHO but still needs help to accept.
SendEchoBelow(p) ==
  /\ p \in correct
  /\ pc[p] = "none"
  /\ Cardinality({q \in correct : MsgTypesFrom(p, q) # {}})
       >= (N - (2 * T))
  /\ Cardinality({q \in AllIds : MsgTypesFrom(p, q) # {}}) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {[snd |-> p, t |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rxMsgs>>

\* With N-T distinct ECHOs, sending ECHO and accepting happen together.
SendEchoAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "none"
  /\ Cardinality({q \in AllIds : MsgTypesFrom(p, q) # {}}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ sentMsgs' = sentMsgs \cup {[snd |-> p, t |-> "ECHO"]}
  /\ UNCHANGED <<correct, faulty, rxMsgs>>

RelayAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality({q \in AllIds : MsgTypesFrom(p, q) # {}}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accept"]
  /\ UNCHANGED <<correct, faulty, rxMsgs, sentMsgs>>

Next ==
  \/ \E p \in correct, msgs \in SUBSET Senders : Recv(p, msgs)
  \/ \E p \in AllIds : BroadcastAccept(p) \/ SendEchoBelow(p) \/ SendEchoAccept(p) \/ RelayAccept(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in correct : WF_vars(Recv(p, { [snd |-> 3, t |-> "ECHO"] }))
  /\ \A p \in correct : WF_vars(Recv(p, { [snd |-> 4, t |-> "ECHO"] }))

\* If the broadcaster never starts, no correct process is justified in accepting.
UnforgLtl == \A i \in correct : pc[i] = "rcvd" ~> (\A j \in correct : pc[j] = "accept")

CorrLtl == \A i \in correct : pc[i] = "rcvd" ~> (\A j \in correct : pc[j] = "accept")

RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A j \in correct : pc[j] = "accept")

FCConstraints ==
  /\ (N > (3 * T))
  /\ (T >= F)
  /\ (F >= 0)

====