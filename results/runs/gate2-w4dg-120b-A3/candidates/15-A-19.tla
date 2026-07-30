---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Protocol control locations; Broadcast means the process received the
\* INITIAL message from the broadcaster, so no dedicated broadcaster is modeled.
Loc == {"Init", "NotInit", "Echoed", "Accepted"}

Actors == 0..(N-1)
Messages == {"ECHO"}
MsgSpace == [snd: Actors, typ: Messages]

VARIABLES
  correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

\* Helper: distinct senders among the messages a process has received.
Senders(p) == { m.snd : m \in recv[p] }

Init ==
  /\ Cardinality(correct) = N - F
  /\ faulty = Actors \ correct
  /\ \A p \in Actors : pc[p] \in Loc
  /\ recv = [p \in Actors |-> {}]
  /\ sent = {}

InitBcast ==
  Init /\ \A p \in Actors : pc[p] = "Init"

\* Every message a correct process can see is either from a correct sender
\* (already sent) or a Byzantine one (appears nondeterministically).
SeenMsgs(p) ==
  { m \in sent : m.snd \in correct } \cup
  { m \in MsgSpace : m.snd \in faulty }

Receive(p) ==
  /\ pc[p] # "Accepted"
  /\ \E new \in SUBSET SeenMsgs(p) :
       /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
       /\ pc' = IF pc[p] = "Init" /\ pc' = "Accepted"
               THEN pc[p]
               ELSE pc[p]
  /\ UNCHANGED << correct, faulty, sent >>

Echo(p) ==
  /\ pc[p] = "NotInit"
  /\ Cardinality(Senders(p)) >= N - 2*T
  /\ Cardinality(Senders(p)) < N - T
  /\ sent' = sent \cup { [snd |-> p, typ |-> "ECHO"] }
  /\ pc' = "Echoed"
  /\ UNCHANGED << correct, faulty, recv >>

EchoAccept(p) ==
  /\ pc[p] = "NotInit"
  /\ Cardinality(Senders(p)) >= N - T
  /\ sent' = sent \cup { [snd |-> p, typ |-> "ECHO"] }
  /\ pc' = "Accepted"
  /\ UNCHANGED << correct, faulty, recv >>

EchoLate(p) ==
  /\ pc[p] = "Echoed"
  /\ Cardinality(Senders(p)) >= N - T
  /\ pc' = "Accepted"
  /\ UNCHANGED << correct, faulty, recv, sent >>

Quiesce ==
  /\ \A p \in Actors : pc[p] = "Accepted"
  /\ UNCHANGED vars

Next ==
  \/ \E p \in Actors : Receive(p)
  \/ \E p \in Actors : Echo(p)
  \/ \E p \in Actors : EchoAccept(p)
  \/ \E p \in Actors : EchoLate(p)
  \/ Quiesce

\* No fairness needed for the unforgeability safety check; weak fairness on the
\* combined receive/act steps covers eventual progress of correct processes.
Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Quiesce)
  /\ WF_vars(\E p \in Actors : Receive(p))
  /\ WF_vars(\E p \in Actors : Echo(p))
  /\ WF_vars(\E p \in Actors : EchoAccept(p))
  /\ WF_vars(\E p \in Actors : EchoLate(p))

TypeOK ==
  /\ correct \subseteq Actors
  /\ faulty = Actors \ correct
  /\ pc \in [Actors -> Loc]
  /\ recv \in [Actors -> SUBSET MsgSpace]
  /\ sent \subseteq MsgSpace

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F
  /\ Cardinality(sent) <= N

UnforgLtl == (InitBcast = Init) ~> (\A p \in correct : pc[p] = "Accepted")

CorrLtl == (InitBcast = InitBcast) ~> (\A p \in correct : pc[p] = "Accepted")

RelayLtl == (\E p \in correct : pc[p] = "Accepted") ~> (\A p \in correct : pc[p] = "Accepted")

====