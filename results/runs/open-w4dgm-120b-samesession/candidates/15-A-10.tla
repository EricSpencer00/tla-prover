---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, inbox, sentMsgs

MessageType == {"ECHO"}

vars == <<correct, faulty, pc, inbox, sentMsgs>>

RECURSIVE SumOf(_)
SumOf(S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE IN (x :> 1 @@ SumOf(S \ {x}))

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty \subseteq (1..N)
  /\ SumOf(pc) = N
  /\ inbox \in [1..N -> SUBSET (1..N \X MessageType)]
  /\ sentMsgs \subseteq (1..N \X MessageType)

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ faulty = (1..N) \ correct
  /\ N > 3 * T

NoInit == Cardinality({i \in correct : pc[i] = 0})

Init ==
  /\ correct = {i \in 1..N : i <= N - F}
  /\ faulty = (1..N) \ correct
  /\ pc = [i \in 1..N |-> IF i <= N - F THEN 0 ELSE 1]
  /\ inbox = [i \in 1..N |-> {}]
  /\ sentMsgs = {}

\* A correct process may receive any subset of everything sent by correct
\* processes, plus any arbitrary Byzantine contribution.
Receive(i) ==
  /\ i \in correct
  /\ \E m \in SUBSET (sentMsgs \X MessageType) :
       inbox' = [inbox EXCEPT ![i] = inbox[i] \cup m]
  /\ UNCHANGED <<correct, faulty, pc, sentMsgs>>

\* Receiving the INIT message (or starting in its broadcast state) triggers a
\* synchronous accept-and-echo without waiting for a quorum.
SendEcho(i) ==
  /\ i \in correct
  /\ pc[i] = 1
  /\ pc' = [pc EXCEPT ![i] = 2]
  /\ sentMsgs' = sentMsgs \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

\* A slow process may wait for messages to accumulate; it sends an echo once
\* enough distinct senders have been heard from, but only accepts a strong
\* quorum.
CatchUp(i) ==
  /\ i \in correct
  /\ pc[i] = 1
  /\ Cardinality(inbox[i]) >= N - 2 * T
  /\ Cardinality(inbox[i]) < N - T
  /\ pc' = [pc EXCEPT ![i] = 2]
  /\ sentMsgs' = sentMsgs \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

Accept(i) ==
  /\ i \in correct
  /\ pc[i] = 1
  /\ Cardinality(inbox[i]) >= N - T
  /\ pc' = [pc EXCEPT ![i] = 2]
  /\ sentMsgs' = sentMsgs \cup {<<i, "ECHO">>}
  /\ UNCHANGED <<correct, faulty, inbox>>

RelayAccept(i) ==
  /\ i \in correct
  /\ pc[i] = 1
  /\ Cardinality(inbox[i]) >= N - T
  /\ pc' = [pc EXCEPT ![i] = 2]
  /\ UNCHANGED <<correct, faulty, inbox, sentMsgs>>

Next == Receive(1) \/ SendEcho(1) \/ CatchUp(1) \/ Accept(1) \/ RelayAccept(1)
      \/ Receive(2) \/ SendEcho(2) \/ CatchUp(2) \/ Accept(2) \/ RelayAccept(2)
      \/ Receive(3) \/ SendEcho(3) \/ CatchUp(3) \/ Accept(3) \/ RelayAccept(3)
      \/ Receive(4) \/ SendEcho(4) \/ CatchUp(4) \/ Accept(4) \/ RelayAccept(4)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Receive(1)) /\ WF_vars(SendEcho(1))
  /\ WF_vars(Receive(2)) /\ WF_vars(SendEcho(2))
  /\ WF_vars(Receive(3)) /\ WF_vars(SendEcho(3))
  /\ WF_vars(Receive(4)) /\ WF_vars(SendEcho(4))

CorrLtl == <>(\A i \in correct : pc[i] = 2)

RelayLtl == (\E i \in correct : pc[i] = 2) ~> (\A i \in correct : pc[i] = 2)

UnforgLtl == NoInit ~> (\A i \in correct : pc[i] = 2)

====