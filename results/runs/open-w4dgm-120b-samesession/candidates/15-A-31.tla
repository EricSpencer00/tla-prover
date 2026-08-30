---- MODULE bcastByz ----
EXTENDS Integers, FiniteSets

CONSTANTS N, T, F

None == "none"
ECHO == "echo"
Locations == {"initstate", "broadcast", "nobroadcast", "echoed", "accepted"}

VARIABLES correct, faulty, role, recv, sent

vars == <<correct, faulty, role, recv, sent>>

InitMsg(k) == IF k \in correct THEN "broadcast" ELSE "nobroadcast"

InitStates == [i \in 1..N |-> IF InitMsg(i) = "broadcast" THEN "broadcast" ELSE "nobroadcast"]
NoRecv == [i \in 1..N |-> {}]
NoSent == {}

TypeOK ==
  /\ correct \subseteq (1..N)
  /\ faulty = (1..N) \ correct
  /\ Cardinality(correct) = N - F
  /\ role \in [1..N -> Locations]
  /\ recv \in [1..N -> SUBSET (1..N \X {"echo"})]
  /\ sent \subseteq (1..N \X {"echo"})

Lagging == {i \in 1..N : role[i] = "echoed" /\ Cardinality(recv[i]) < N - T}

Init ==
  /\ correct = {i \in 1..N : F > 0 /\ (i - 1) % (F + 1) \in 1..(N - F)}
  /\ role = InitStates
  /\ recv = NoRecv
  /\ sent = NoSent

NoBroadcastInit ==
  /\ role = [i \in 1..N |-> "nobroadcast"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Receive(i, msgs) ==
  /\ role[i] \in {"initstate", "nobroadcast"}
  /\ msgs \subseteq sent \cup (faulty \X {ECHO})
  /\ recv' = [recv EXCEPT ![i] = msgs]
  /\ role' = [role EXCEPT ![i] = IF msgs = {} THEN role[i] ELSE "initstate"]
  /\ UNCHANGED <<correct, faulty, sent>>

EchoAndAccept(i) ==
  /\ role[i] = "initstate"
  /\ sent' = sent \cup {<<i, ECHO>>}
  /\ role' = [role EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv>>

EchoNoAccept(i) ==
  /\ role[i] \in {"nobroadcast", "initstate"}
  /\ Cardinality(recv[i]) >= N - 2 * T
  /\ Cardinality(recv[i]) < N - T
  /\ sent' = sent \cup {<<i, ECHO>>}
  /\ role' = [role EXCEPT ![i] = "echoed"]
  /\ UNCHANGED <<correct, faulty, recv>>

EchoAndAcceptLater(i) ==
  /\ role[i] \in {"nobroadcast", "initstate"}
  /\ Cardinality(recv[i]) >= N - T
  /\ sent' = sent \cup {<<i, ECHO>>}
  /\ role' = [role EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv>>

LaggingAccept(i) ==
  /\ role[i] = "echoed"
  /\ Cardinality(recv[i]) >= N - T
  /\ role' = [role EXCEPT ![i] = "accepted"]
  /\ UNCHANGED <<correct, faulty, recv, sent>>

Next ==
  \/ \E i \in 1..N, msgs \in SUBSET (1..N \X {"echo"}) : Receive(i, msgs)
  \/ \E i \in 1..N : EchoAndAccept(i) \/ EchoNoAccept(i) \/ EchoAndAcceptLater(i) \/ LaggingAccept(i)
  \/ UnchangedVars

PostInit == Init \/ NoBroadcastInit

Spec == PostInit /\ [][Next]_vars /\ WF_vars(\E i \in 1..N : EchoAndAccept(i))
                    /\ WF_vars(\E i \in 1..N : EchoAndAcceptLater(i))
                    /\ WF_vars(\E i \in 1..N : LaggingAccept(i))

FCConstraints == Lagging = {}

UnforgLtl == (\A i \in 1..N : role[i] = "nobroadcast") ~> (\A i \in 1..N : role[i] = "accepted")

CorrLtl == (\A i \in 1..N : role[i] = "broadcast") ~> (\A i \in 1..N : role[i] = "accepted")

RelayLtl == (\E i \in 1..N : role[i] = "accepted") ~> (\A i \in 1..N : role[i] = "accepted")

====