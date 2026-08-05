---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A one-round reliable broadcast tolerant to up to T Byzantine processes
\* (Srikanth-Toueg 1987, Fig. 7) where the "INIT broadcast" is modeled as an
\* initial value per process rather than a dedicated broadcaster. A process
\* accepts once it receives enough ECHO messages; Byzantine senders may
\* inject arbitrary messages. The model checks that no INIT broadcast can
\* be forged by a process whose initial value was "no broadcast".
Messages == {"echomsg"}
Ids == {1..N}
CorrectIds == {i \in Ids : i <= N - F}
FaultyIds == Ids \ CorrectIds

VARIABLES correct, faulty, pc, recv, sent

vars == <<correct, faulty, pc, recv, sent>>

TypeOK ==
  /\ correct \subseteq Ids
  /\ faulty \subseteq Ids
  /\ correct \cap faulty = {}
  /\ pc \in [Ids -> {"nobroadcast", "receive", "echoed", "accept"}]
  /\ recv \in [Ids -> SUBSET (Ids \X Messages)]
  /\ sent \in SUBSET (Ids \X Messages)

Init ==
  /\ correct = CorrectIds
  /\ faulty = FaultyIds
  /\ pc = [i \in Ids |-> IF i <= N - F THEN "receive" ELSE "nobroadcast"]
  /\ recv = [i \in Ids |-> {}]
  /\ sent = {}

\* A correct process nondeterministically receives any new messages from
\* correct senders and any possible Byzantine messages.
Receive(i, newmsg) ==
  /\ i \in correct
  /\ newmsg \subseteq ({j \in correct : <<j, "echomsg">> \in sent}
                       \cup (faulty \X Messages))
  /\ recv' = [recv EXCEPT ![i] = recv[i] \cup newmsg]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

\* A process starts broadcasting (echoing) immediately on receipt of the
\* INIT broadcast, and accepts at the same step.
BroadcastFromInit(i) ==
  /\ i \in correct
  /\ pc[i] = "receive"
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<<i, "echomsg">>}
  /\ UNCHANGED <<correct, faulty, recv>>

EchoLater(i) ==
  /\ i \in correct
  /\ pc[i] \in {"nobroadcast", "echoed"}
  /\ Cardinality({j \in Ids : <<j, "echomsg">> \in recv[i]}) >= N - 2 * T
  /\ Cardinality({j \in Ids : <<j, "echomsg">> \in recv[i]}) < N - T
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ sent' = sent \cup {<<i, "echomsg">>}
  /\ UNCHANGED <<correct, faulty, recv>>

EchoAndAccept(i) ==
  /\ i \in correct
  /\ pc[i] \in {"nobroadcast", "echoed"}
  /\ Cardinality({j \in Ids : <<j, "echomsg">> \in recv[i]}) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ sent' = sent \cup {<<i, "echomsg">>}
  /\ UNCHANGED <<correct, faulty, recv>>

AcceptLater(i) ==
  /\ i \in correct
  /\ pc[i] = "echoed"
  /\ Cardinality({j \in Ids : <<j, "echomsg">> \in recv[i]}) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accept"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E i \in Ids, newmsg \in SUBSET (Ids \X Messages) : Receive(i, newmsg)
  \/ \E i \in Ids : BroadcastFromInit(i) \/ EchoLater(i) \/ EchoAndAccept(i) \/ AcceptLater(i)

Spec == Init /\ [][Next]_vars
FairSpec == Spec /\ WF_vars(\E i \in Ids, newmsg \in SUBSET (Ids \X Messages) : Receive(i, newmsg))
CorrLtl == (pc[1] = "receive") ~> (\A i \in correct : pc[i] = "accept")
RelayLtl == (\E i \in correct : pc[i] = "accept") ~> (\A i \in correct : pc[i] = "accept")

\* Unforgeability: with no INIT broadcast (no process starts in the
\* "receive" state), no correct process can ever accept.
UnforgLtl == (\A i \in correct : pc[i] # "receive") ~> (\A i \in correct : pc[i] # "accept")

FCConstraints == N > 3 * T /\ T >= F /\ F >= 0

====