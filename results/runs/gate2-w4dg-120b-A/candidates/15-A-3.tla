---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent

vars == << correct, faulty, pc, recv, sent >>

Procs == 0 .. (N - 1)

InitType == "none"
BroadState == "broadcast"
NoBroadState == "nobroadcast"
SendState == "sent"
AcceptState == "accept"

InitVariations == {BroadState, NoBroadState}

PCValues == {InitType, BroadState, NoBroadState, SendState, AcceptState}

MsgTypes == {"ECHO"}

TypeOK ==
  /\ correct \subseteq Procs
  /\ \A x \in correct : x < N
  /\ faulty \subseteq Procs
  /\ \A x \in faulty : x < N
  /\ correct \cap faulty = {}
  /\ correct \cup faulty = Procs
  /\ pc \in [Procs -> PCValues]
  /\ recv \in [Procs -> SUBSET (MsgTypes \X Procs)]
  /\ sent \subseteq (MsgTypes \X Procs)

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ correct = { x \in Procs : x < N - F }
  /\ faulty = Procs \ correct

InitBase(ini) ==
  /\ pc = [x \in Procs |-> IF x \in correct THEN ini ELSE InitType]
  /\ recv = [x \in Procs |-> {}]
  /\ sent = {}

InitDefault == InitBase(BroadState)
InitNobroad == InitBase(NoBroadState)

CorrectlyReceived(x) == Cardinality({ m \in recv[x] : m[1] \in correct })

ReceiveMsgs(x, mset) ==
  /\ pc[x] \in {BroadState, NoBroadState}
  /\ mset \subseteq (sent \cup (MsgTypes \X faulty))
  /\ recv' = [recv EXCEPT ![x] = recv[x] \cup mset]
  /\ UNCHANGED << correct, faulty, pc, sent >>

SendEcho(x) ==
  /\ x \in correct
  /\ pc[x] = InitType
  /\ pc' = [pc EXCEPT ![x] = SendState]
  /\ sent' = sent \cup ({ << "ECHO", x >> })
  /\ UNCHANGED << correct, faulty, recv >>

AcceptFromInit(x) ==
  /\ x \in correct
  /\ pc[x] = InitType
  /\ pc' = [pc EXCEPT ![x] = AcceptState]
  /\ sent' = sent \cup ({ << "ECHO", x >> })
  /\ UNCHANGED << correct, faulty, recv >>

SendEchoLate(x) ==
  /\ x \in correct
  /\ pc[x] = InitType
  /\ CorrectlyReceived(x) >= N - 2 * T
  /\ CorrectlyReceived(x) < (N - T)
  /\ pc' = [pc EXCEPT ![x] = SendState]
  /\ sent' = sent \cup ({ << "ECHO", x >> })
  /\ UNCHANGED << correct, faulty, recv >>

AcceptLate(x) ==
  /\ x \in correct
  /\ pc[x] = InitType
  /\ CorrectlyReceived(x) >= N - T
  /\ pc' = [pc EXCEPT ![x] = AcceptState]
  /\ sent' = sent \cup ({ << "ECHO", x >> })
  /\ UNCHANGED << correct, faulty, recv >>

AcceptAfterSend(x) ==
  /\ x \in correct
  /\ pc[x] = SendState
  /\ CorrectlyReceived(x) >= N - T
  /\ pc' = [pc EXCEPT ![x] = AcceptState]
  /\ UNCHANGED << correct, faulty, recv, sent >>

ReceiveStep ==
  \E x \in Procs :
    \/ \E mset \in SUBSET (MsgTypes \X Procs) : ReceiveMsgs(x, mset)
    \/ SendEcho(x) \/ AcceptFromInit(x)
    \/ SendEchoLate(x) \/ AcceptLate(x)
    \/ AcceptAfterSend(x)

Next ==
  \/ ReceiveStep

Spec ==
  /\ InitDefault
  /\ [][Next]_vars
  /\ WF_vars(ReceiveStep)

CorrLtl ==
  ( \A x \in correct : pc[x] = BroadState ) ~> ( \A x \in correct : pc[x] = AcceptState )

RelayLtl == ( \E x \in correct : pc[x] = AcceptState ) ~> ( \A x \in correct : pc[x] = AcceptState )

UnforgLtl ==
  /\ InitNobroad ~> ( \A x \in correct : pc[x] = AcceptState )
  /\ ( \A x \in correct : pc[x] # AcceptState ) ~> ( \A x \in correct : pc[x] = AcceptState )

====