---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Procs == 1..N
SentMsgs == {"echo1", "echo2"}
\* The sender identity is the message; that is how the model rules out a
\* forged "echo from nowhere" even when a Byzantine process does send one.
MsgSpace == Procs \X SentMsgs
NoOne == 0
NoMsgs == {}

VARIABLES correct, faulty, pc, recv, sentBy

vars == << correct, faulty, pc, recv, sentBy >>

TypeOK ==
  /\ correct \subseteq Procs
  /\ faulty \subseteq Procs
  /\ pc \in [Procs -> {"init", "nobroadcast", "sent", "acpt"}]
  /\ recv \in [Procs -> SUBSET MsgSpace]
  /\ sentBy \in SUBSET MsgSpace

\* A correct process accepts only after N-T participants sent ECHO, so even
\* the T faulty processes can never unilaterally make an accept happen.
FCConstraints ==
  /\ correct \cup faulty = Procs
  /\ correct \cap faulty = {}
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) <= T

Init ==
  /\ correct = {1..(N - F)}
  /\ faulty = {(N - F + 1)..N}
  /\ sentBy = NoMsgs
  /\ pc = [p \in Procs |-> IF p <= (N - F) THEN "init" ELSE "nobroadcast"]
  /\ recv = [p \in Procs |-> NoMsgs]

\* Correct processes only ever receive messages that some correct process
\* actually sent, combined with whatever arbitrary traffic the Byzantine
\* processes (the bounded set of the model) happen to throw in.
ReceiveMsgs(p) ==
  /\ p \in correct
  /\ recv' = [recv EXCEPT ![p] =
        recv[p] \cup (sentBy \cup (faulty \X SentMsgs))]
  /\ UNCHANGED << correct, faulty, pc, sentBy >>

SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "init"
  /\ sentBy' = sentBy \cup (p \X SentMsgs)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ UNCHANGED << correct, faulty, recv >>

SendEchoOnN2T(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"sent", "acpt"}
  /\ Cardinality(recv[p]) >= N - 2 * T
  /\ Cardinality(recv[p]) < N - T
  /\ sentBy' = sentBy \cup (p \X SentMsgs)
  /\ pc' = [pc EXCEPT ![p] = "sent"]
  /\ UNCHANGED << correct, faulty, recv >>

SendEchoOnNT(p) ==
  /\ p \in correct
  /\ pc[p] \notin {"sent", "acpt"}
  /\ Cardinality(recv[p]) >= N - T
  /\ sentBy' = sentBy \cup (p \X SentMsgs)
  /\ pc' = [pc EXCEPT ![p] = "acpt"]
  /\ UNCHANGED << correct, faulty, recv >>

AcceptOnNT(p) ==
  /\ p \in correct
  /\ pc[p] = "sent"
  /\ Cardinality(recv[p]) >= N - T
  /\ pc' = [pc EXCEPT ![p] = "acpt"]
  /\ UNCHANGED << correct, faulty, recv, sentBy >>

Next ==
  \/ \E p \in Procs : ReceiveMsgs(p)
  \/ \E p \in Procs : SendEcho(p)
  \/ \E p \in Procs : SendEchoOnN2T(p)
  \/ \E p \in Procs : SendEchoOnNT(p)
  \/ \E p \in Procs : AcceptOnNT(p)

Spec == Init /\ [][Next]_vars
        /\ \A p \in Procs : WF_vars(ReceiveMsgs(p))
        /\ \A p \in Procs : WF_vars(SendEcho(p))
        /\ \A p \in Procs : WF_vars(SendEchoOnNT(p))
        /\ \A p \in Procs : WF_vars(AcceptOnNT(p))

CorrLtl == <>(\A p \in correct : pc[p] = "acpt")
RelayLtl == (\E p \in correct : pc[p] = "acpt") ~> (\A p \in correct : pc[p] = "acpt")

\* If no correct process ever broadcast, none should ever accept.
UnforgLtl == (\A p \in correct : pc[p] \in {"nobroadcast", "sent"}) ~>
              (\A p \in correct : pc[p] = "nobroadcast")

====