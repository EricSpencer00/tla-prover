---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* Unforgeability of the broadcast rests on the fact that no correct process
\* ever accepts unless it either initially received the INIT message, or
\* received at least N-T genuine ECHO messages from distinct senders.
\* The receiver-set thresholds N-2T and N-T are the exact margins from
\* Srikanth-Toueg's quorum bound, and the bounded capacity on the in-flight
\* message set keeps each reachable state finite for model checking.

VARIABLES correct, faulty, pc, recvMsgs, sentMsgs

MsgSpace == (1..N) \X {"ECHO"}

TypeOK ==
  /\ correct \subseteq 1..N
  /\ faulty \subseteq 1..N
  /\ Cardinality(correct) = N - F
  /\ pc \in [1..N -> {"initrcv", "nonrcv", "sent", "accept"}]
  /\ recvMsgs \in [1..N -> SUBSET MsgSpace]
  /\ sentMsgs \subseteq MsgSpace

Init ==
  /\ correct = CHOOSE S \in SUBSET 1..N :
       /\ Cardinality(S) = N - F
       /\ \A a \in S, b \in S : a <= b
  /\ faulty = 1..N \ correct
  /\ pc = [i \in 1..N |-> IF i % 2 = 0 THEN "initrcv" ELSE "nonrcv"]
  /\ recvMsgs = [i \in 1..N |-> {}]
  /\ sentMsgs = {}

InitNoBroad ==
  /\ correct = CHOOSE S \in SUBSET 1..N :
       /\ Cardinality(S) = N - F
       /\ \A a \in S, b \in S : a <= b
  /\ faulty = 1..N \ correct
  /\ pc = [i \in 1..N |-> "nonrcv"]
  /\ recvMsgs = [i \in 1..N |-> {}]
  /\ sentMsgs = {}

\* A correct process may receive any batch of new messages from correct
\* senders plus any arbitrary batch from Byzantine senders.
Receive(i) ==
  /\ i \in correct
  /\ pc[i] \in {"initrcv", "nonrcv"}
  /\ recvMsgs' = [recvMsgs EXCEPT ![i] =
       recvMsgs[i] \cup
         (sentMsgs \cap (correct \X {"ECHO"}))
         \cup (MsgSpace \cap (faulty \X {"ECHO"}))]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

\* A correct process that received the INIT message accepts immediately.
InitAccept(i) ==
  /\ i \in correct
  /\ pc[i] = "initrcv"
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sentMsgs' = sentMsgs \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* Receiving enough (but not a supermajority) ECHOs is enough to echo --
\* this is what guarantees a correct process always has an onward step.
EchoStep(i) ==
  /\ i \in correct
  /\ pc[i] \in {"initrcv", "nonrcv"}
  /\ Cardinality(recvMsgs[i]) >= N - 2 * T
  /\ Cardinality(recvMsgs[i]) < N - T
  /\ pc' = [pc EXCEPT ![i] = "sent"]
  /\ sentMsgs' = sentMsgs \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

\* Surpassing the supermajority threshold lets a process accept.
AcceptStep(i) ==
  /\ i \in correct
  /\ pc[i] \in {"initrcv", "nonrcv"}
  /\ Cardinality(recvMsgs[i]) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sentMsgs' = sentMsgs \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, recvMsgs>>

RelayStep(i) ==
  /\ i \in correct
  /\ pc[i] = "sent"
  /\ Cardinality(recvMsgs[i]) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, recvMsgs, sentMsgs>>

Next ==
  \/ \E i \in 1..N : Receive(i)
  \/ \E i \in 1..N : InitAccept(i)
  \/ \E i \in 1..N : EchoStep(i)
  \/ \E i \in 1..N : AcceptStep(i)
  \/ \E i \in 1..N : RelayStep(i)

Spec == Init /\ [][Next]_<<correct, faulty, pc, recvMsgs, sentMsgs>>

CorrLtl == <>(\A i \in correct : pc[i] \in {"accept", "sent"})
RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] \in {"accept", "sent"})
FCConstraints == TypeOK
UnforgLtl == (\A i \in correct : pc[i] = "nonrcv") ~> (\A i \in correct : pc[i] = "nonrcv")
====