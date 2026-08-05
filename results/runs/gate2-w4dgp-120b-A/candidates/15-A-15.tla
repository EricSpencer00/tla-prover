---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets

CONSTANTS N, T, F

\* A broadcast message is modeled as a process's initial state (BRCV for "got
\* the broadcaster's INIT", NOTBRCV otherwise); an ECHO is always an explicit
\* message in transit and is the only type of message that Byzantine processes
\* are assumed capable of inventing.

Processes == 1..N
Locs == {"notbrrcv", "brrcv", "echoed", "accepted"}
Msgs == {"ECHO"}

RECURSIVE UnionOf(_, _)
UnionOf(f, S) == IF S = {} THEN {}
                 ELSE LET x == CHOOSE y \in S : TRUE IN f[x] \cup UnionOf(f, S \ {x})

VARIABLES correct, faulty, pc, recv, sentBy
vars == << correct, faulty, pc, recv, sentBy >>

\* Received ECHOs are counted by distinct sender identity, so a Byzantine
\* process can flood with duplicates but that does not help reach the quorum.
ReceivedEchos(i) == { x \in recv[i] : snd == x /\ type == "ECHO" }

InitState ==
  \E X \in [Processes -> Locs] :
    /\ Cardinality({i \in Processes : X[i] = "brrcv"}) = 0
    /\ correct = {i \in Processes : X[i] \in {"brrcv", "echoed", "accepted"}}
    /\ faulty = {i \in Processes : X[i] # "brrcv"}
    /\ pc = X
    /\ recv = [i \in Processes |-> {}]
    /\ sentBy = {}

Init ==
  \E X \in [Processes -> Locs] :
    /\ Cardinality({i \in Processes : X[i] = "brrcv"}) = N - F
    /\ correct = {i \in Processes : X[i] \in {"brrcv", "echoed", "accepted"}}
    /\ faulty = {i \in Processes : X[i] # "brrcv"}
    /\ pc = X
    /\ recv = [i \in Processes |-> {}]
    /\ sentBy = {}

\* Any-but-not-all messages from Byzantine processes may be missing at any
\* moment, so a correct process may always receive more.
RecvMsgs(i) ==
  \E m \in [sentBy \cup {j \in faulty : {<<j, "ECHO">>}} -> BOOLEAN] :
    /\ m \in sendBy \cup {<<j, "ECHO">> : j \in faulty}
    /\ recv' = [recv EXCEPT ![i] = recv[i] \cup {m}]

Echo(i) == <<i, "ECHO">>

\* A process that itself got the broadcast (the usual case) accepts immediately
\* upon sending its first ECHO.
SendAndAccept(i) ==
  /\ pc[i] = "brrcv"
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentBy' = sentBy \cup {Echo(i)}
  /\ UNCHANGED <<correct, faulty, recv>>

SendEcho(i) ==
  /\ pc[i] \in {"brrcv", "echoed"}
  /\ Cardinality(ReceivedEchos(i)) >= N - 2 * T
  /\ Cardinality(ReceivedEchos(i)) < N - T
  /\ pc' = [pc EXCEPT ![i] = "echoed"]
  /\ sentBy' = sentBy \cup {Echo(i)}
  /\ UNCHANGED <<correct, faulty, recv>>

SendAndAcceptQuorum(i) ==
  /\ pc[i] = "brrcv"
  /\ Cardinality(ReceivedEchos(i)) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ sentBy' = sentBy \cup {Echo(i)}
  /\ UNCHANGED <<correct, faulty, recv>>

Accept(i) ==
  /\ pc[i] = "echoed"
  /\ Cardinality(ReceivedEchos(i)) >= N - T
  /\ pc' = [pc EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sentBy>>

Next ==
  \/ \E i \in correct : RecvMsgs(i) /\ SendAndAccept(i)
  \/ \E i \in correct : RecvMsgs(i) /\ SendEcho(i)
  \/ \E i \in correct : RecvMsgs(i) /\ SendAndAcceptQuorum(i)
  \/ \E i \in correct : RecvMsgs(i) /\ Accept(i)
  \/ InitState

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E i \in correct : RecvMsgs(i))
  /\ SF_vars(\E i \in correct : SendAndAccept(i))

NoBroadcast == \A i \in correct : pc[i] # "brrcv"
AllBroadcast == \A i \in correct : pc[i] = "brrcv"

\* Unforgeability: if no correct process ever broadcast, none can ever accept.
UnforgLtl == NoBroadcast ~> (\A i \in correct : pc[i] = "accepted")
FCConstraints == N > 3 * T /\ T >= F /\ F >= 0
CorrLtl == AllBroadcast ~> (\A i \in correct : pc[i] = "accepted")
RelayLtl == (\E i \in correct : pc[i] = "accepted")
~> (\A i \in correct : pc[i] = "accepted")
TypeOK ==
  /\ correct \subseteq Processes
  /\ pc \in [Processes -> Locs]
  /\ recv \in [Processes -> SUBSET (Processes \X Msgs)]
  /\ sentBy \subseteq (Processes \X Msgs)

====