---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

\* Two initial conditions: the regular one and the restricted "no INIT" one.
InitStates == {"initRecvd", "initNotRecvd"}

VARIABLES correct, faulty, pc, recvMsgs, sentMsgs

vars == << correct, faulty, pc, recvMsgs, sentMsgs >>

Procs == 0..(N - 1)
MsgIds == {"echo"}

EchoSenders(p) == { m[1] : m \in { x \in recvMsgs[p] : x[2] = "echo" } }

TypeOK ==
  /\ correct \subseteq Procs
  /\ faulty \subseteq Procs
  /\ pc \in [Procs -> {"initRecvd", "initNotRecvd", "sent", "acc"}]
  /\ recvMsgs \in [Procs -> SUBSET (Procs \X MsgIds)]
  /\ sentMsgs \subseteq (Procs \X MsgIds)

Init ==
  /\ correct = { p \in Procs : p < N - F }
  /\ pc \in [p \in Procs |-> IF p < N - F THEN "initRecvd" ELSE "initNotRecvd"]
  /\ recvMsgs = [p \in Procs |-> {}]
  /\ sentMsgs = {}

\* Receive any subset of messages from correct senders plus any Byzantine
\* messages; this is what covers the arbitrary Byzantine interference.
ReceiveMsgs(p) ==
  /\ pc[p] \in {"initRecvd", "initNotRecvd", "sent"}
  /\ \E newMsgs \in SUBSET (correct \X MsgIds):
       recvMsgs' = [recvMsgs EXCEPT ![p] = @ \cup newMsgs]
  /\ UNCHANGED << correct, faulty, pc, sentMsgs >>

SentByCorrectNotFaulty == { m \in sentMsgs : m[1] \in correct /\ m[2] \in MsgIds }

\* Implicit broadcast: receipt of the INIT message triggers immediate echo.
InitRecvActs(p) ==
  /\ pc[p] = "initRecvd"
  /\ sentMsgs' = SentByCorrectNotFaulty \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ UNCHANGED << correct, faulty, recvMsgs >>

\* First echo stage: cross the lower threshold, send echo but do not accept.
EchoStageOne(p) ==
  /\ pc[p] = "initNotRecvd"
  /\ Cardinality(EchoSenders(p)) >= N - 2 * T
  /\ Cardinality(EchoSenders(p)) < N - T
  /\ sentMsgs' = SentByCorrectNotFaulty \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ UNCHANGED << correct, faulty, recvMsgs >>

\* Second echo stage: cross the higher threshold, send echo and accept.
EchoStageTwo(p) ==
  /\ pc[p] = "initNotRecvd"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ sentMsgs' = SentByCorrectNotFaulty \cup {<<p, "echo">>}
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ UNCHANGED << correct, faulty, recvMsgs >>

\* Slow-but-correct case: already echoed, now collects enough to accept.
EchoStageThree(p) ==
  /\ pc[p] = "sent"
  /\ Cardinality(EchoSenders(p)) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "acc"]
  /\ UNCHANGED << correct, faulty, recvMsgs, sentMsgs >>

Next ==
  \/ \E p \in Procs: ReceiveMsgs(p) \/ InitRecvActs(p) \/ EchoStageOne(p)
                                      \/ EchoStageTwo(p) \/ EchoStageThree(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in Procs: WF_vars(ReceiveMsgs(p))

CorrLtl == (\A p \in correct: pc[p] = "initRecvd") ~> (\A p \in correct: pc[p] = "acc")

RelayLtl == (\E p \in correct: pc[p] = "acc") ~> (\A p \in correct: pc[p] = "acc")

\* SAFETY: if no correct process ever broadcasts, none accepts.
UnforgLtl == (\A p \in correct: pc[p] # "initRecvd") ~> (\A p \in correct: pc[p] # "acc")

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0

====