---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, loc, recvBuf, sentMsgs

vars == <<correct, faulty, loc, recvBuf, sentMsgs>>

\* Types: loc is the control location; recvBuf[u] is the set of (sender,kind)
\* messages u has received; sentMsgs is the send frontier from correct nodes.
MsgKinds == {"init", "echo"}

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN f[x] + SumOf(f, S \ {x})

TypeOK ==
  /\ correct \subseteq (1..N) /\ faulty \subseteq (1..N)
  /\ loc \in [1..N -> {"none", "init", "echoed", "acpt"}]
  /\ recvBuf \in [1..N -> SUBSET (1..N \X MsgKinds)]
  /\ sentMsgs \subseteq (1..N \X MsgKinds)

\* Faulty nodes can forge messages; unforgeability is about correct nodes only.
FCConstraints ==
  /\ loc \in [1..N -> {"none", "init", "echoed", "acpt"}]
  /\ SumOf([u \in 1..N |-> IF loc[u] = "acpt" THEN 1 ELSE 0], 1..N) \in 0..N

Init ==
  /\ correct = 1..(N - F) /\ faulty = (N - F + 1)..N
  /\ loc = [u \in 1..N |-> "none"]
  /\ recvBuf = [u \in 1..N |-> {}]
  /\ sentMsgs = {}

\* The restricted start: no correct process broadcast (all lacking the INIT).
InitNoBroad ==
  /\ Init
  /\ \A u \in correct : loc[u] = "none"
  /\ UNCHANGED <<correct, faulty>>

\* Correct nodes only ever receive messages that have actually been sent by
\* correct senders, plus any forged messages from Byzantine nodes.
Receive(u, m) ==
  /\ u \in correct
  /\ m \in sentMsgs \cup (faulty \X MsgKinds)
  /\ m \notin recvBuf[u]
  /\ recvBuf' = [recvBuf EXCEPT ![u] = @ \cup {m}]
  /\ UNCHANGED <<correct, faulty, loc, sentMsgs>>

\* The single-step receive-and-act rule that fairness below is applied to.
ReceiveAny(u) ==
  \E m \in (sentMsgs \cup (faulty \X MsgKinds)) : Receive(u, m)

EchoSet(u) == {s \in 1..N : <<s, "echo">> \in recvBuf[u]}

\* A correct node that received the INIT accepts and broadcasts ECHO.
InitAct(u) ==
  /\ u \in correct
  /\ loc[u] = "init"
  /\ loc' = [loc EXCEPT ![u] = "acpt"]
  /\ sentMsgs' = sentMsgs \cup {<<u, "echo">>}
  /\ UNCHANGED <<correct, faulty, recvBuf>>

\* Sending ECHO is separate from accepting, at two different quorum thresholds.
EchoMid(u) ==
  /\ u \in correct
  /\ loc[u] = "none"
  /\ Cardinality(EchoSet(u)) >= N - 2*T
  /\ Cardinality(EchoSet(u)) < N - T
  /\ loc' = [loc EXCEPT ![u] = "echoed"]
  /\ sentMsgs' = sentMsgs \cup {<<u, "echo">>}
  /\ UNCHANGED <<correct, faulty, recvBuf>>

EchoAcpt(u) ==
  /\ u \in correct
  /\ loc[u] = "none"
  /\ Cardinality(EchoSet(u)) >= N - T
  /\ loc' = [loc EXCEPT ![u] = "acpt"]
  /\ sentMsgs' = sentMsgs \cup {<<u, "echo">>}
  /\ UNCHANGED <<correct, faulty, recvBuf>>

Relay(u) ==
  /\ u \in correct
  /\ loc[u] = "echoed"
  /\ Cardinality(EchoSet(u)) >= N - T
  /\ loc' = [loc EXCEPT ![u] = "acpt"]
  /\ UNCHANGED <<correct, faulty, recvBuf, sentMsgs>>

Next ==
  \/ InitNoBroad
  \/ \E u \in 1..N : ReceiveAny(u) \/ InitAct(u) \/ EchoMid(u) \/ EchoAcpt(u) \/ Relay(u)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A u \in 1..N : WF_vars(ReceiveAny(u))
  /\ \A u \in correct : SF_vars(EchoMid(u))
  /\ \A u \in correct : SF_vars(EchoAcpt(u))
  /\ \A u \in correct : WF_vars(InitAct(u))
  /\ \A u \in correct : WF_vars(Relay(u))

\* If everybody got the INIT broadcast, correctness demands everybody accepts.
CorrLtl == \A u \in correct : (loc[u] = "init") ~> (loc[u] = "acpt")
RelayLtl == (\E u \in correct : loc[u] = "acpt") ~> (\A u \in correct : loc[u] = "acpt")

\* With no correct broadcaster the unforgeability statement applies to correct
\* nodes only, though Byzantine nodes may still broadcast and echo.
UnforgLtl == (\A u \in correct : loc[u] = "none") ~> (\A u \in correct : loc[u] = "acpt")

====