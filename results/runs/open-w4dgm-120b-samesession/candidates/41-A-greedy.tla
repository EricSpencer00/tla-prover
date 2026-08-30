---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process tracks a suspicion set, a per-peer timeout interval, a
\* per-peer last-heard counter, a local clock, and its outgoing messages.
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

\* Send alive messages to every other process at a send tick.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in suspect[p] /\ lastHeard[q] < timeout[p]
                        THEN lastHeard[q] + 1 ELSE lastHeard[q]]
    /\ UNCHANGED <<suspect, timeout>>

\* Predict crashes when a peer has not been heard from past its timeout.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [q \in Proc |->
                     IF q \in suspect[p] \/ lastHeard[q] > timeout[p]
                     THEN suspect[p] \cup {q} ELSE suspect[p]]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in suspect[p] /\ lastHeard[q] < timeout[p]
                        THEN lastHeard[q] + 1 ELSE lastHeard[q]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<timeout, outbox>>

\* Receive messages; a message from a suspected peer clears the suspicion
\* and, if the peer was suspected, expands its timeout (adaptive).
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E m \in outbox[p] :
        /\ suspect' = suspect[p] \ {m.from}
        /\ timeout' = [timeout EXCEPT ![m.from] =
                         IF m.from \in suspect[p] THEN @ + 1 ELSE @]
        /\ lastHeard' = [lastHeard EXCEPT ![m.from] = 0]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]

\* The local clock is bounded: it resets once it passes every relevant bound.
ResetClock(p) ==
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > timeout[q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_vars

====