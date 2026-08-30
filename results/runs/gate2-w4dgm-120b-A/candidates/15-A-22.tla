---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A broadcast message is represented by an "INIT" control value at the sender.
\* ECHO messages are sent by correct processes and forged by any Byzantine sender.

\* Types: loc=control location, src=process id, kind=message tag, msgs=pair set.
Loc == {"initRcv", "noInit", "sentEcho", "accepted"}
Src == 1..N
Kind == {"INIT", "ECHO"}
Msgs == Src \X Kind

VARIABLES pc, recvMsgs, sentEcho, correct, faulty

vars == <<pc, recvMsgs, sentEcho, correct, faulty>>

TypeOK ==
  /\ pc \in [Src -> Loc]
  /\ recvMsgs \in [Src -> SUBSET Msgs]
  /\ sentEcho \subseteq Src
  /\ correct \subseteq Src
  /\ faulty \subseteq Src

FCConstraints ==
  /\ correct \cup faulty = Src
  /\ correct \cap faulty = {}
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

\* Receive fresh messages from correct and Byzantine processes (bounded to what is
\* currently available from each) -- the unfair step of the protocol.
ReceiveStep ==
  /\ \E p \in Src:
       \E newMsgs \subseteq (sentEcho \X {"ECHO"}) \cup (faulty \X {"ECHO"}):
         recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup newMsgs]
  /\ UNCHANGED <<pc, sentEcho, correct, faulty>>

SendEchoStep ==
  /\ \E p \in correct:
       /\ pc[p] \in {"initRcv", "noInit"}
       /\ sentEcho' = sentEcho \cup {p}
       /\ pc' = [pc EXCEPT ![p] = "sentEcho"]
  /\ UNCHANGED <<recvMsgs, correct, faulty>>

\* Two acceptance thresholds: N-2T for a lagging participant, N-T for a quorum.
AcceptStep ==
  /\ \E p \in correct:
       /\ pc[p] # "accepted"
       /\ Cardinality({m \in recvMsgs[p] : m[2] = "ECHO"}) >= N - 2 * T
       /\ sentEcho' = sentEcho \cup {p}
       /\ pc' = [pc EXCEPT ![p] = IF Cardinality({m \in recvMsgs[p] : m[2] = "ECHO"}) >= N - T
                                 THEN "accepted" ELSE "sentEcho"]
  /\ UNCHANGED <<recvMsgs, correct, faulty>>

\* A lagging participant that receives a stricter quorum eventually accepts.
PendingAcceptStep ==
  /\ \E p \in correct:
       /\ pc[p] = "sentEcho"
       /\ Cardinality({m \in recvMsgs[p] : m[2] = "ECHO"}) >= N - T
       /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED <<recvMsgs, sentEcho, correct, faulty>>

Next ==
  \/ ReceiveStep
  \/ SendEchoStep
  \/ AcceptStep
  \/ PendingAcceptStep

Spec ==
  /\ Init
  /\ WF_vars(ReceiveStep)
  /\ WF_vars(SendEchoStep)
  /\ WF_vars(AcceptStep)
  /\ SF_vars(PendingAcceptStep)

\* Unforgeability: if no correct process broadcasts, none ever accepts.
Unforgeable == (\A p \in correct : pc[p] # "initRcv") ~> (\A p \in correct : pc[p] = "accepted")

Init ==
  /\ pc \in [Src -> {"initRcv", "noInit"}]
  /\ recvMsgs = [p \in Src |-> {}]
  /\ sentEcho = {}
  /\ \E c \in SUBSET Src:
       /\ Cardinality(c) = N - F
       /\ correct = c
       /\ faulty = Src \ c

InitNoBroadcast ==
  /\ Init
  /\ \A p \in correct : pc[p] = "noInit"

\* If every correct participant received the broadcast, they all accept.
CorrLtl == (\A p \in correct : pc[p] = "initRcv") ~> (\A p \in correct : pc[p] = "accepted")

\* Once any correct participant accepts, all correct participants accept.
RelayLtl == \E p \in correct : pc[p] = "accepted" ~> (\A q \in correct : pc[q] = "accepted")

\* When no one broadcasts, unforgeability is not a vacuous truth.
UnforgLtl == (InitNoBroadcast) => Unforgeable

====