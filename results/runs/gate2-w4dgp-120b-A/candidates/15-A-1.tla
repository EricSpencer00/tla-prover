---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N > 3 * T /\ T >= F /\ F >= 0

AllProc == 0 .. (N - 1)
MsgType == {"ECHO"}
Msgs == AllProc \X MsgType

VARIABLES correct, faulty, pc, rcv, sends
vars == << correct, faulty, pc, rcv, sends >>

TypeOK ==
  /\ correct \subseteq AllProc /\ faulty \subseteq AllProc
  /\ correct \cup faulty = AllProc /\ correct \cap faulty = {}
  /\ pc \in [AllProc -> 0 .. 3]
  /\ rcv \in [AllProc -> SUBSET Msgs]
  /\ sends \subseteq (AllProc \X MsgType)

FCConstraints ==
  /\ Cardinality(correct) = N - F
  /\ Cardinality(faulty) = F

Init ==
  /\ \E g \in (AllProc \ {0}) :
       correct = (AllProc \ {0}) \cup {g} /\ pc = [p \in AllProc |-> IF p = 0 \/ p = g THEN 1 ELSE 0]
  /\ sends = {}
  /\ rcv = [p \in AllProc |-> {}]

InitNoBroadcast ==
  /\ correct = AllProc
  /\ pc = [p \in AllProc |-> 0]
  /\ sends = {}
  /\ rcv = [p \in AllProc |-> {}]

\* Correct processes receive any subset of messages sent by correct
\* processes together with any messages a Byzantine process may forge.
Recv(p) ==
  /\ pc[p] <= 1
  /\ \E M \subseteq (sends \cup (faulty \X MsgType)) :
       /\ rcv' = [rcv EXCEPT ![p] = M]
       /\ pc' = [pc EXCEPT ![p] = IF M = {} THEN pc[p] ELSE 1]
  /\ UNCHANGED << correct, faulty, sends >>

\* A correct process that started with the broadcast accepts and sends ECHO.
Act1(p) ==
  /\ pc[p] = 1
  /\ sends' = sends \cup {<<p, "ECHO">>}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED << correct, faulty, rcv >>

\* With an intermediate quorum, a correct process sends ECHO but does not accept.
Act2(p) ==
  /\ pc[p] = 0
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in rcv[p]}) >= N - 2 * T
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in rcv[p]}) < N - T
  /\ sends' = sends \cup {<<p, "ECHO">>}
  /\ pc' = [pc EXCEPT ![p] = 1]
  /\ UNCHANGED << correct, faulty, rcv >>

\* With a strong quorum, a correct process sends ECHO and accepts.
Act3(p) ==
  /\ pc[p] < 2
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in rcv[p]}) >= N - T
  /\ sends' = sends \cup {<<p, "ECHO">>}
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED << correct, faulty, rcv >>

\* A process that already sent ECHO accepts upon a strong quorum.
Act4(p) ==
  /\ pc[p] = 1
  /\ Cardinality({q \in correct : <<q, "ECHO">> \in rcv[p]}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = 2]
  /\ UNCHANGED << correct, faulty, rcv, sends >>

Next ==
  \/ \E p \in correct : Recv(p) \/ Act1(p) \/ Act2(p) \/ Act3(p) \/ Act4(p)
  \/ UNCHANGED vars

Spec ==
  /\ Init \/ InitNoBroadcast
  /\ [][Next]_vars
  /\ WF_vars(\E p \in correct : Recv(p))
  /\ WF_vars(\E p \in correct : Act1(p))
  /\ WF_vars(\E p \in correct : Act2(p))
  /\ WF_vars(\E p \in correct : Act3(p))
  /\ WF_vars(\E p \in correct : Act4(p))

\* If no correct process broadcasts, no correct process accepts.
UnforgLtl == (\A p \in correct : pc[p] = 0) ~> (\A p \in correct : pc[p] = 2) \/ (\A p \in correct : pc[p] = 0)

CorrLtl == (\A p \in correct : pc[p] = 1) ~> (\A p \in correct : pc[p] = 2)
RelayLtl == (\E p \in correct : pc[p] = 2) ~> (\A p \in correct : pc[p] = 2)

====