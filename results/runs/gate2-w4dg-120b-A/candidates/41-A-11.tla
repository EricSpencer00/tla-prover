---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

\* A message carries the addressed process and the process that sent it
Message == [to: Proc, from: Proc]

VARIABLES
    suspect,
    timeout,
    lastHeard,
    clock,
    toSend

vars == <<suspect, timeout, lastHeard, clock, toSend>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ toSend \in [Proc -> SUBSET Message]

\* Every clock begins before the first send-predict threshold
Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ toSend = [p \in Proc |-> {}]

\* Alive messages are emitted at the send interval, never at the predict interval
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ toSend' = [toSend EXCEPT ![p] = { [to |-> q, from |-> p] : q \in Proc }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in Proc /\ q # p /\ q \notin suspect[p] THEN
                            lastHeard[q] + 1 ELSE lastHeard[q]]
    /\ UNCHANGED <<suspect, timeout>>

\* Predictions are made at the predict interval, never at the send interval
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [p \in Proc |->
                        IF p \in Proc THEN suspect[p]
                        UNION { q \in Proc : lastHeard[q] > timeout[q] } ELSE suspect[p]]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in Proc THEN lastHeard[q] + 1 ELSE lastHeard[q]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<timeout, toSend>>

\* Receiving acts at all other clock values; messages that arrive cancel suspicion
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ suspect' = [p \in Proc |->
                        IF p \in Proc THEN suspect[p] \ { m.from : m \in toSend[p] } ELSE suspect[p]]
    /\ timeout' = [p \in Proc |->
                        timeout[p] + Cardinality({ m \in toSend[p] : m.from \in suspect[p] })]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in { m.from : m \in toSend[p] } THEN 0 ELSE lastHeard[q]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint /\ clock[p] + 1 > d0 + 1
                                         THEN 0 ELSE clock[p] + 1]
    /\ toSend' = [toSend EXCEPT ![p] = {}]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====