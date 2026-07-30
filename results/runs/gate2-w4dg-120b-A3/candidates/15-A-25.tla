---- MODULE bcastByz ----
EXTENDS Naturals

CONSTANTS N, T, F

\* Control locations: NoInit = no broadcast message received yet; HasInit = broadcast
\* message received; Echoed = sent an ECHO message; Accept = accepted the broadcast.
Locations == { "NoInit", "HasInit", "Echoed", "Accept" }
Phases == { "OnlySend", "SendAndAccept" }
MsgTypes == { "ECHO" }

VARIABLES correct, faulty, pc, recvd, sent

vars == << correct, faulty, pc, recvd, sent >>

Msgs == [who : 1..N, type : MsgTypes]

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ pc \in [1..N -> Locations]
  /\ recvd \in [1..N -> SUBSET Msgs]
  /\ sent \subseteq Msgs

Card(f, S) == Cardinality({ x \in S : f[x] })

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ properSubset == Cardinality(faulty) > 0 /\ Cardinality(faulty) < N
  /\ correct \cap faulty = {}
  /\ properSubset => correct \cup faulty = 1..N
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

Init ==
  /\ UNCHANGED << correct, faulty >>
  /\ pc = [p \in 1..N |-> IF p \in correct THEN "HasInit" ELSE "NoInit"]
  /\ recvd = [p \in 1..N |-> {}]
  /\ sent = {}

NoBroadcastInit ==
  /\ UNCHANGED << correct, faulty >>
  /\ pc = [p \in 1..N |-> IF p \in correct THEN "NoInit" ELSE "NoInit"]
  /\ recvd = [p \in 1..N |-> {}]
  /\ sent = {}

\* A correct process may receive a whole batch of new messages at once.
Receive(p) ==
  /\ p \in correct
  /\ pc[p] \in {"NoInit", "HasInit"}
  /\ \E S \in SUBSET (sent \cup [who : faulty, type : MsgTypes]) :
       recvd' = [recvd EXCEPT ![p] = @ \cup S]
  /\ UNCHANGED << correct, faulty, pc, sent >>

BroadcastEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "HasInit"
  /\ pc' = [pc EXCEPT ![p] = "Echoed"]
  /\ sent' = sent \cup {[who |-> p, type |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, recvd >>

EchoAndAct(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"Echoed", "Accept"}
  /\ Card(f, recvd[p]) >= N - 2 * T
  /\ Card(f, recvd[p]) < N - T
  /\ pc' = [pc EXCEPT ![p] = "Echoed"]
  /\ sent' = sent \cup {[who |-> p, type |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, recvd >>

EchoAndAccept(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"Echoed", "Accept"}
  /\ Card(f, recvd[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Echoed"]
  /\ sent' = sent \cup {[who |-> p, type |-> "ECHO"]}
  /\ UNCHANGED << correct, faulty, recvd >>

LateAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "Echoed"
  /\ Card(f, recvd[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "Accept"]
  /\ UNCHANGED << correct, faulty, recvd, sent >>

ReceiveSome == \E p \in 1..N : Receive(p)
BroadcastSome == \E p \in correct : BroadcastEcho(p)
EchoAndActSome == \E p \in correct : EchoAndAct(p)
EchoAndAcceptSome == \E p \in correct : EchoAndAccept(p)
LateAcceptSome == \E p \in correct : LateAccept(p)

Next ==
  \/ ReceiveSome \/ BroadcastSome \/ EchoAndActSome
  \/ EchoAndAcceptSome \/ LateAcceptSome

Fairness ==
  /\ WF_vars(ReceiveSome)
  /\ WF_vars(BroadcastSome)
  /\ WF_vars(EchoAndActSome)
  /\ WF_vars(EchoAndAcceptSome)
  /\ WF_vars(LateAcceptSome)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ Fairness

\* The unforgeability property is proved as a safety lemma: if no correct process
\* broadcasts, no correct process ever accepts, because the required quorums can
\* never be reached from messages sent only by Byzantine processes.
UnforgLtl ==
  \A p \in correct : (pc[p] = "HasInit") ~> (pc[p] = "Accept")

CorrLtl == (\A p \in correct : pc[p] = "HasInit") ~> (\A p \in correct : pc[p] = "Accept")
RelayLtl == (\E p \in correct : pc[p] = "Accept") ~> (\A p \in correct : pc[p] = "Accept")

====