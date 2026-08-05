---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

ASSUME N > 3 * T

VARIABLES correct, faulty, pc, recvd, sent
vars == <<correct, faulty, pc, recvd, sent>>

RECURSIVE UnionOf(_, _)
UnionOf(f, S) ==
  IF S = {} THEN {}
  ELSE LET x == CHOOSE y \in S : TRUE
           rest == UnionOf(f, S \ {x})
       IN f[x] \cup rest

ProcessIds == 0..(N - 1)
Msgs == {"ECHO"}
MsgPairs == ProcessIds \X Msgs

RecvInit == {"init"}
StateS0 == "s0"
StateS1 == "s1"
StateECHO == "echo"
StateAccept == "accept"

InitCorrect ==
  {x \in ProcessIds : Cardinality({y \in ProcessIds : y < x}) < N - F}
InitFaulty == ProcessIds \ InitCorrect

InitRecvdFull ==
  [p \in ProcessIds |-> IF p \in InitCorrect THEN RecvInit ELSE {}]

TypeOK ==
  /\ correct \subseteq ProcessIds
  /\ faulty \subseteq ProcessIds
  /\ correct \cup faulty = ProcessIds
  /\ \A p \in ProcessIds : pc[p] \in {StateS0, StateS1, StateECHO, StateAccept}
  /\ \A p \in ProcessIds : recvd[p] \subseteq MsgPairs
  /\ sent \subseteq MsgPairs

FCConstraints == Cardinality(faulty) <= F /\ N > 3 * T

Init ==
  /\ correct = InitCorrect
  /\ faulty = InitFaulty
  /\ pc = InitRecvdFull
  /\ recvd = [p \in ProcessIds |-> {}]
  /\ sent = {}

Receive(p, msgs) ==
  /\ pc[p] \in {StateS0, StateS1}
  /\ pc[p] # StateAccept
  /\ msgs # {}
  /\ msgs \subseteq sent \cup (faulty \X Msgs)
  /\ recvd' = [recvd EXCEPT ![p] = recvd[p] \cup msgs]
  /\ UNCHANGED <<correct, faulty, pc, sent>>

SendEcho(p) ==
  /\ pc[p] = StateS0
  /\ RecvInit \subseteq recvd[p]
  /\ pc' = [pc EXCEPT ![p] = StateAccept]
  /\ sent' = sent \cup (correct \X {"ECHO"})
  /\ UNCHANGED <<correct, faulty, recvd>>

RelayEcho(p) ==
  /\ pc[p] = StateS0
  /\ RecvInit \notin recvd[p]
  /\ Cardinality(recvr) >= N - 2 * T
  /\ Cardinality(recvr) < N - T
  /\ pc' = [pc EXCEPT ![p] = StateECHO]
  /\ sent' = sent \cup (correct \X {"ECHO"})
  /\ UNCHANGED <<correct, faulty, recvd>>
  where recvr == {q \in ProcessIds : <<q, "ECHO">> \in recvd[p]}

AcceptRelay(p) ==
  /\ pc[p] = StateS0
  /\ RecvInit \notin recvd[p]
  /\ Cardinality(recvr) >= N - T
  /\ pc' = [pc EXCEPT ![p] = StateAccept]
  /\ sent' = sent \cup (correct \X {"ECHO"})
  /\ UNCHANGED <<correct, faulty, recvd>>
  where recvr == {q \in ProcessIds : <<q, "ECHO">> \in recvd[p]}

AcceptEcho(p) ==
  /\ pc[p] \in {StateECHO, StateS0}
  /\ Cardinality(recvr) >= N - T
  /\ pc' = [pc EXCEPT ![p] = StateAccept]
  /\ UNCHANGED <<correct, faulty, recvd, sent>>
  where recvr == {q \in ProcessIds : <<q, "ECHO">> \in recvd[p]}

Next ==
  \/ \E p \in correct, msgs \in SUBSET MsgPairs : Receive(p, msgs)
  \/ \E p \in correct : SendEcho(p)
  \/ \E p \in correct : RelayEcho(p)
  \/ \E p \in correct : AcceptRelay(p)
  \/ \E p \in correct : AcceptEcho(p)

Spec == Init /\ [][Next]_vars
FairSpec ==
  Init /\ [][Next]_vars
  /\ \A p \in correct : WF_vars(\E msgs \in SUBSET MsgPairs : Receive(p, msgs))

CorrLtl == ( \A p \in correct : RecvInit \in recvd[p] ) ~> ( \A p \in correct : pc[p] = StateAccept )
RelayLtl == ( \E p \in correct : pc[p] = StateAccept ) ~> ( \A p \in correct : pc[p] = StateAccept )
UnforgLtl == ( \A p \in correct : RecvInit \notin recvd[p] ) ~> ( \A p \in correct : pc[p] # StateAccept )

====