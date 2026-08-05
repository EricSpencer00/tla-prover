---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

Processes == 1..N
Messages == {1..N}
ECHO == "ECHO"

VARIABLES correctProcs, faultyProcs, pc, received, sentMsgs

vars == <<correctProcs, faultyProcs, pc, received, sentMsgs>>

RECURSIVE UnionOf(_, _)
UnionOf(f, S) == IF S = {} THEN {}
                 ELSE LET x == CHOOSE y \in S : TRUE
                      IN f[x] \cup UnionOf(f, S \ {x})

InitState == 1
NoInitState == 2
SentState == 3
AcceptedState == 4

TypeOK ==
  /\ correctProcs \subseteq Processes
  /\ faultyProcs \subseteq Processes
  /\ correctProcs \cup faultyProcs = Processes
  /\ correctProcs \cap faultyProcs = {}
  /\ pc \in [Processes -> {InitState, NoInitState, SentState, AcceptedState}]
  /\ received \in [Processes -> SUBSET (Messages \X {ECHO})]
  /\ sentMsgs \subseteq Messages

FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(correctProcs) = N - F

NoBroadcastInit == UNION { {p} : p \in correctProcs }

Init ==
  /\ UNCHANGED <<correctProcs, faultyProcs, sentMsgs>>
  /\ \E S \in SUBSET Processes :
       /\ Cardinality(S) = N - F
       /\ correctProcs = S
       /\ faultyProcs = Processes \ S
  /\ UNION { {p} : p \in correctProcs } = NoBroadcastInit
  /\ \E S \in SUBSET Processes :
       /\ Cardinality(S) = N
       /\ \A p \in Processes : pc' = [pc EXCEPT ![p] = IF p \in S THEN InitState ELSE NoInitState]
  /\ \A p \in Processes : received' = [received EXCEPT ![p] = {}]
  /\ UNCHANGED sentMsgs

Receive(p) ==
  /\ pc[p] \in {InitState, NoInitState, SentState}
  /\ \E m \in UNION { {x} : x \in sentMsgs \cup Messages } :
       /\ received' = [received EXCEPT ![p] = received[p] \cup m]
  /\ UNCHANGED <<correctProcs, faultyProcs, pc, sentMsgs>>

SendEcho(p) ==
  /\ pc[p] \in {InitState, NoInitState}
  /\ pc' = [pc EXCEPT ![p] = SentState]
  /\ sentMsgs' = sentMsgs \cup {p}
  /\ UNCHANGED <<correctProcs, faultyProcs, received>>

ActOnEcho(p) ==
  /\ pc[p] = NoInitState
  /\ Cardinality({m \in received[p] : m[2] = ECHO}) >= N - 2 * T
  /\ Cardinality({m \in received[p] : m[2] = ECHO}) < N - T
  /\ pc' = [pc EXCEPT ![p] = SentState]
  /\ sentMsgs' = sentMsgs \cup {p}
  /\ UNCHANGED <<correctProcs, faultyProcs, received>>

AcceptOnEcho(p) ==
  /\ pc[p] = SentState
  /\ Cardinality({m \in received[p] : m[2] = ECHO}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = AcceptedState]
  /\ UNCHANGED <<correctProcs, faultyProcs, received, sentMsgs>>

ActOnEchoAfterSend(p) ==
  /\ pc[p] = SentState
  /\ Cardinality({m \in received[p] : m[2] = ECHO}) >= N - T
  /\ pc' = [pc EXCEPT ![p] = AcceptedState]
  /\ UNCHANGED <<correctProcs, faultyProcs, received, sentMsgs>>

Next ==
  \/ Init
  \/ \E p \in Processes : Receive(p)
  \/ \E p \in Processes : SendEcho(p)
  \/ \E p \in Processes : ActOnEcho(p)
  \/ \E p \in Processes : AcceptOnEcho(p)
  \/ \E p \in Processes : ActOnEchoAfterSend(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ \A p \in Processes : WF_vars(Receive(p))
  /\ \A p \in Processes : WF_vars(SendEcho(p))

SpecNoFair == Init /\ [][Next]_vars

CorrLtl == (\A p \in correctProcs : pc[p] = InitState) ~> (\A p \in correctProcs : pc[p] = AcceptedState)

RelayLtl == (\E p \in correctProcs : pc[p] = AcceptedState) ~> (\A p \in correctProcs : pc[p] = AcceptedState)

UnforgLtl == NoBroadcastInit ~> (\A p \in correctProcs : pc[p] # AcceptedState)

====