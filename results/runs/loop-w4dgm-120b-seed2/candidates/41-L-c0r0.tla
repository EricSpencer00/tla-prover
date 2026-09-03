---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process tracks who it suspects, per-process timeout intervals, and a
\* per-process counter of ticks since it last heard from that process.
VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* Send alive messages to every other process; this never coincides with Predict.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |->
                        IF q = p \/ lastHeard[q] >= timeout[q] THEN @ ELSE @ + 1]
    /\ UNCHANGED <<suspect, timeout>>

\* Predict crashes: suspect any process from which nothing has been heard within
\* that process's timeout interval.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup
                        {q \in Proc : q # p /\ lastHeard[q] > timeout[q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |->
                        IF q = p \/ lastHeard[q] >= timeout[q] THEN @ ELSE @ + 1]
    /\ UNCHANGED <<timeout, outbox>>

\* Receive messages; a message from a suspected process clears the suspicion and
\* raises that process's timeout interval (adaptive timeout).
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E m \in outbox[p] :
        /\ lastHeard' = [lastHeard EXCEPT ![m.from] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![m.from] = IF @ < timeout[m.from] + 1
                                                    THEN @ + 1 ELSE @]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]

\* The local clock is bounded: once it exceeds every relevant threshold it resets.
Tick(p) ==
    /\ clock[p] > 0
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > timeout[q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : Tick(p)

Spec == Init /\ [][Next]_vars

====