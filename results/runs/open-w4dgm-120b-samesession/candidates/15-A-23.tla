---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Correct processes follow the one-round broadcast protocol; faulty (Byzantine)
\* processes may send arbitrary ECHO messages. N > 3T is the safety threshold.
\* Unforgeability: no correct process accepts without any correct process broadcasting.
\* Fault tolerance: up to T faulty processes are modeled, with F of them acting.

Participants == 1..N
MsgTypes == {"ECHO"}
QNONE == "qnone"
QINIT == "qinit"
QEBCAST == "qebcast"
QRECV == "qrecv"
QACC == "qacc"
MaxMsgs == N * Cardinality(MsgTypes)

VARIABLES correct, faulty, pc, recvMsgs, sentMsgs

vars == <<correct, faulty, pc, recvMsgs, sentMsgs>>

TypeOK ==
  /\ correct \subseteq Participants
  /\ faulty \subseteq Participants
  /\ pc \in [Participants -> {QNONE, QINIT, QEBCAST, QRECV, QACC}]
  /\ recvMsgs \in [Participants -> SUBSET (Participants \X MsgTypes)]
  /\ sentMsgs \subseteq (Participants \X MsgTypes)

\* Two initial states: unrestricted (any mix of broadcast / non-broadcast) and
\* the restricted one where no correct process broadcasts initially.
Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = Participants \ correct
  /\ pc \in [Participants -> {QINIT, QNONE}]
  /\ recvMsgs = [p \in Participants |-> {}]
  /\ sentMsgs = {}

InitNoBroadcast ==
  /\ Cardinality(correct) = N - F
  /\ faulty = Participants \ correct
  /\ pc = [p \in Participants |-> QNONE]
  /\ recvMsgs = [p \in Participants |-> {}]
  /\ sentMsgs = {}

NextBcast ==
  \E p \in correct:
    /\ pc[p] # QACC
    /\ pc' = [pc EXCEPT ![p] = QEBCAST]
    /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
    /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* A correct process may receive any subset of what correct senders broadcast
\* plus any arbitrary message from a Byzantine sender.
Receive(p, S) ==
  /\ pc[p] # QACC
  /\ recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup S]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

\* Immediate accept if broadcast was received.
RecAccept(p) ==
  /\ pc[p] = QINIT
  /\ pc' = [pc EXCEPT ![p] = QACC]
  /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* Below quorum: send ECHO but no accept yet (any-to-any dispatching).
RecEchobelow(p) ==
  /\ pc[p] = QNONE
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recvMsgs[p]}) >= N - 2 * T
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recvMsgs[p]}) < N - T
  /\ pc' = [pc EXCEPT ![p] = QEBCAST]
  /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

RecEchoAbove(p) ==
  /\ pc[p] = QNONE
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recvMsgs[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = QACC]
  /\ sentMsgs' = sentMsgs \cup {<<p, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

RecAccept(p) ==
  /\ pc[p] = QEBCAST
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in recvMsgs[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = QACC]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

Next ==
  \/ NextBcast
  \/ \E p \in Participants, S \in SUBSET (Participants \X MsgTypes): Receive(p, S)
  \/ \E p \in Participants: RecAccept(p) \/ RecEchobelow(p) \/ RecEchoAbove(p) \/ RecAccept(p)

Spec == Init /\ [][Next]_vars
SpecNoBcast == InitNoBroadcast /\ [][Next]_vars

FCConstraints ==
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = Participants
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

UnforgLtl == InitNoBroadcast => (\A p \in correct: pc[p] # QACC)

\* Correctness: if the broadcaster reaches every correct process, all accept.
CorrLtl == (\A p \in correct: pc[p] = QINIT) ~> (\A q \in correct: pc[q] = QACC)

\* Relay: one acceptance among correct processes drags the rest along.
RelayLtl == (\E p \in correct: pc[p] = QACC) ~> (\A q \in correct: pc[q] = QACC)

====