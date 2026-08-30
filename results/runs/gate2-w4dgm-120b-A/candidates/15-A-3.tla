---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Each process is either correct or a Byzantine (faulty) participant.
\* initState models whether the broadcaster's single INIT message was
\* received at each process (true = received) or not.
\* Messages are of type "ECHO" paired with the sending process id.

VARIABLES correct, faulty, pc, recvMsgs, sentMsgs

vars == << correct, faulty, pc, recvMsgs, sentMsgs >>

Processes == 0..(N - 1)
ECHO == "ECHO"
Msgs == [sender: Processes, typ: {ECHO}]
NoMsg == [sender |-> 0, typ |-> ECHO]

TypeOK ==
  /\ correct \subseteq Processes
  /\ faulty \subseteq Processes
  /\ pc \in [Processes -> {"broadcast", "nobroadcast", "sent", "accepted"}]
  /\ recvMsgs \in [Processes -> SUBSET Msgs]
  /\ sentMsgs \subseteq Msgs

Init ==
  /\ correct = {p \in Processes : p < (N - F)}
  /\ faulty = {p \in Processes : p >= (N - F)}
  /\ pc = [p \in Processes |-> IF p < (N - F) THEN "broadcast" ELSE "nobroadcast"]
  /\ recvMsgs = [p \in Processes |-> {}]
  /\ sentMsgs = {}

\* Messages are delivered in batches: a correct process collects any
\* subset of all messages sent by correct processes plus any possible
\* Byzantine message (an arbitrary $noMsg is always available).
ReceiveBatch(p) ==
  /\ pc[p] \in {"broadcast", "nobroadcast"}
  /\ \E m \in SUBSET (sentMsgs \cup {NoMsg}) :
       /\ recvMsgs' = [recvMsgs EXCEPT ![p] = recvMsgs[p] \cup m]
  /\ UNCHANGED << correct, faulty, pc, sentMsgs >>

EchoAndAccept(p) ==
  /\ pc[p] = "broadcast"
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> p, typ |-> ECHO]}
  /\ UNCHANGED << correct, faulty, recvMsgs >>

EchoOnSupermajority(p) ==
  /\ pc[p] = "nobroadcast"
  /\ Cardinality({m \in recvMsgs[p] : m.typ = ECHO}) >= (N - 2 * T)
  /\ Cardinality({m \in recvMsgs[p] : m.typ = ECHO}) < (N - T)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> p, typ |-> ECHO]}
  /\ UNCHANGED << correct, faulty, recvMsgs >>

EchoAndAcceptOnMajority(p) ==
  /\ pc[p] = "nobroadcast"
  /\ Cardinality({m \in recvMsgs[p] : m.typ = ECHO}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ sentMsgs' = sentMsgs \cup {[sender |-> p, typ |-> ECHO]}
  /\ UNCHANGED << correct, faulty, recvMsgs >>

AcceptOnMajority(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality({m \in recvMsgs[p] : m.typ = ECHO}) >= (N - T)
  /\ pc' = [pc EXCEPT ![p] = "accepted"]
  /\ UNCHANGED << correct, faulty, recvMsgs, sentMsgs >>

Next ==
  \/ \E p \in Processes : ReceiveBatch(p)
  \/ \E p \in correct : EchoAndAccept(p)
  \/ \E p \in correct : EchoOnSupermajority(p)
  \/ \E p \in correct : EchoAndAcceptOnMajority(p)
  \/ \E p \in correct : AcceptOnMajority(p)

Spec == Init /\ [][Next]_vars
  /\ \A p \in correct : WF_vars(ReceiveBatch(p))
  /\ \A p \in correct : WF_vars(EchoAndAccept(p))
  /\ \A p \in correct : WF_vars(EchoOnSupermajority(p))
  /\ \A p \in correct : WF_vars(EchoAndAcceptOnMajority(p))
  /\ \A p \in correct : WF_vars(AcceptOnMajority(p))

CorrLtl == <>(\A p \in correct : pc[p] = "accepted")
RelayLtl == (\E p \in correct : pc[p] = "accepted") ~> (\A p \in correct : pc[p] = "accepted")
UnforgLtl == (\A p \in correct : pc[p] = "nobroadcast") ~> (\A p \in correct : pc[p] \in {"nobroadcast", "sent"})
FCConstraints == N > (3 * T) /\ T >= F /\ F >= 0

====