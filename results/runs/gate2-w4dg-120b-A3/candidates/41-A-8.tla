---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

\* Per-process state: suspicion set, per-target timeout intervals, per-target
\* last-heard counter, local clock, and the set of outgoing messages.
VARIABLES
    suspect,
    timeout,
    lastHeard,
    clock,
    outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* Send alive messages at a send-multiple clock tick (never coinciding with a
\* predict-multiple tick), advancing the local clock and aging unseen targets.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to # p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF timeout[p][q] < clock[p] + 1 THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

\* Predict crashed processes at a predict-multiple clock tick, suspecting any
\* target whose last-heard counter has passed its timeout interval.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> @ + 1]]
    /\ UNCHANGED <<timeout, outbox>>

\* Receive incoming alive messages at all other clock ticks, resetting
\* last-heard counters, clearing suspicions, and adapting timeouts.
Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E rec \in [Proc -> BOOLEAN] :
         /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF rec[q] THEN 0 ELSE IF @ < timeout[p][q] THEN @ + 1 ELSE @]]
         /\ suspect' = [suspect EXCEPT ![p] = {q \in @ : ~rec[q]}]
         /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |-> IF suspect[p][q] /\ rec[q] THEN @ + 1 ELSE @]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint /\ \A q \in Proc : clock[p] + 1 > timeout[p][q] THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED outbox

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====