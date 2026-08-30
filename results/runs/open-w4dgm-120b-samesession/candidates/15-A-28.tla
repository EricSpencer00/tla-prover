---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A correct process is modelled by its PC/Msgs state; faulty processes simply
\* inject arbitrary ECHO messages and never act on anything themselves.
\* No-broadcast unforgeability is a safety property of the PC variables, so
\* fairness is only needed for the liveness properties, not for safety.

Phases == {"NoEcho", "Sent", "Accepted"}

VARIABLES correctSet, faultySet, pc, msgsRcvd, sentMsgs

vars == <<correctSet, faultySet, pc, msgsRcvd, sentMsgs>>

Nodes == 0..(N-1)
Echos == [snd: Nodes, typ: {"ECHO"}]

TypeOK ==
  /\ correctSet \subseteq Nodes
  /\ faultySet = Nodes \ correctSet
  /\ Cardinality(correctSet) = N - F
  /\ pc \in [Nodes -> Phases]
  /\ msgsRcvd \in [Nodes -> SUBSET Echos]
  /\ sentMsgs \subseteq Echos

Init ==
  /\ \E S \in SUBSET Nodes : Cardinality(S) = N - F /\ correctSet = S
  /\ faultySet = Nodes \ correctSet
  /\ pc = [n \in Nodes |-> IF n < N - F - F THEN "NoEcho" ELSE "Sent"]
  /\ msgsRcvd = [n \in Nodes |-> {}]
  /\ sentMsgs = {}

InitNoBroadcast ==
  /\ \E S \in SUBSET Nodes : Cardinality(S) = N - F /\ correctSet = S
  /\ faultySet = Nodes \ correctSet
  /\ pc = [n \in Nodes |-> "NoEcho"]
  /\ msgsRcvd = [n \in Nodes |-> {}]
  /\ sentMsgs = {}

\* Faulty nodes may inject any ECHO message, correct nodes only resend what
\* they have already broadcast.
Inject(n) == [snd |-> n, typ |-> "ECHO"]
AnyFaultyEcho == UNION { {Inject(n)} : n \in faultySet }
CorrectEchoes(n) == { m \in sentMsgs : m.snd \in correctSet }

Receive(n) ==
  /\ pc[n] \in {"NoEcho", "Sent"}
  /\ msgsRcvd' = [msgsRcvd EXCEPT ![n] = msgsRcvd[n] \cup sentMsgs \cup AnyFaultyEcho]
  /\ UNCHANGED <<correctSet, faultySet, pc, sentMsgs>>

SendEcho(n) ==
  /\ pc[n] \in {"NoEcho", "Sent"}
  /\ sentMsgs' = sentMsgs \cup {Inject(n)}
  /\ pc' = [pc EXCEPT ![n] = "Sent"]
  /\ UNCHANGED <<correctSet, faultySet, msgsRcvd>>

AcceptOnFewer(n) ==
  /\ pc[n] = "NoEcho"
  /\ Cardinality({ m \in msgsRcvd[n] : m.typ = "ECHO" }) >= N - 2 * T
  /\ Cardinality({ m \in msgsRcvd[n] : m.typ = "ECHO" }) < N - T
  /\ sentMsgs' = sentMsgs \cup {Inject(n)}
  /\ pc' = [pc EXCEPT ![n] = "Sent"]
  /\ UNCHANGED <<correctSet, faultySet, msgsRcvd>>

AcceptOnMost(n) ==
  /\ pc[n] \in {"NoEcho", "Sent"}
  /\ Cardinality({ m \in msgsRcvd[n] : m.typ = "ECHO" }) >= N - T
  /\ sentMsgs' = sentMsgs \cup {Inject(n)}
  /\ pc' = [pc EXCEPT ![n] = "Accepted"]
  /\ UNCHANGED <<correctSet, faultySet, msgsRcvd>>

AcceptAfterSent(n) ==
  /\ pc[n] = "Sent"
  /\ Cardinality({ m \in msgsRcvd[n] : m.typ = "ECHO" }) >= N - T
  /\ pc' = [pc EXCEPT ![n] = "Accepted"]
  /\ UNCHANGED <<correctSet, faultySet, msgsRcvd, sentMsgs>>

ReceiveStep == \E n \in Nodes : Receive(n)
SendStep == \E n \in Nodes : SendEcho(n)
AcceptStep == \E n \in Nodes : AcceptOnFewer(n) \/ AcceptOnMost(n) \/ AcceptAfterSent(n)

Next == ReceiveStep \/ SendStep \/ AcceptStep

Spec == Init /\ [][Next]_vars /\ WF_vars(ReceiveStep) /\ WF_vars(SendStep) /\ WF_vars(AcceptStep)

CorrLtl == (\A n \in correctSet : pc[n] = "Sent") ~> (\A n \in correctSet : pc[n] = "Accepted")
RelayLtl == (\E n \in correctSet : pc[n] = "Accepted") ~> (\A n \in correctSet : pc[n] = "Accepted")
UnforgLtl == (\A n \in correctSet : pc[n] # "Sent") => (\A n \in correctSet : pc[n] # "Accepted")

FCConstraints == NoBroadcastImpliesNoAccept
====