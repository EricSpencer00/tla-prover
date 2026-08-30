---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,         \* set of processes (each acts as both sender and receiver)
    d0,           \* default timeout interval
    SendPoint,    \* interval at which alive messages are sent
    PredictPoint, \* interval at which crash predictions are made
    Messages      \* set of actual alive messages in flight

\* One module per process; msgFrom identifies the sender of an alive message.
Message == [msgFrom : Proc]

VARIABLES clock, suspect, timeout, lastHeard, outgoing

vars == <<clock, suspect, timeout, lastHeard, outgoing>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ outgoing \in [Proc -> SUBSET Message]

Init ==
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ suspect = [p \in Proc |-> {}]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

\* Alive messages are sent at every multiple of SendPoint that is not a predict.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] =
                        {[msgFrom |-> q] : q \in Proc \ {p}}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF q \in suspect[p]
                                THEN lastHeard[p][q]
                                ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspect, timeout>>

\* Predictions are made at every multiple of PredictPoint that is not a send.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] =
                        {q \in Proc : q # p /\ lastHeard[p][q] >= timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF q \in suspect[p]
                                THEN lastHeard[p][q]
                                ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outgoing>>

\* Receivers consume messages at all other clock values, clearing suspicion.
Receive(p) ==
    /\ clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0
    /\ \E m \in outgoing[p] : TRUE
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {[m.msgFrom] : m \in outgoing[p]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF \E m \in outgoing[p] : m.msgFrom = q
                                THEN 0
                                ELSE lastHeard[p][q]]]
    /\ timeout' = [timeout EXCEPT ![p] =
                        [q \in Proc |->
                            IF (\E m \in outgoing[p] : m.msgFrom = q) /\ q \in suspect[p]
                                THEN timeout[p][q] + 1
                                ELSE timeout[p][q]]]
    /\ outgoing' = [outgoing EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] > 2 * Max(SendPoint, PredictPoint, d0)
                                      THEN 0 ELSE clock[p] + 1]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

\* Constraint: send and predict clocks are never allowed to coincide.
ClockCoherence ==
    /\ SendPoint \in Nat /\ SendPoint > 0
    /\ PredictPoint \in Nat /\ PredictPoint > 0
    /\ SendPoint % PredictPoint # 0
    /\ PredictPoint % SendPoint # 0

====