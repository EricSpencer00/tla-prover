---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each alive message is addressed from one process to another.
\* The clock-driven regime guarantees send and predict never overlap.
Msg == [from : Proc, to : Proc]

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup
                        {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p, m) ==
    /\ m \in outbox[p]
    /\ outbox' = [outbox EXCEPT ![p] = @ \ {m}]
    /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
    /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
    /\ timeout' = [timeout EXCEPT ![p][m.from] =
                        IF m.from \in suspect[p] THEN @ + 1 ELSE @]
    /\ UNCHANGED clock

\* The clock is bounded, never drifted; once past every trigger it resets.
Tick(p) ==
    /\ clock[p] > 0
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
    \E p \in Proc :
        \/ SendAlive(p) \/ Predict(p) \/ Tick(p)
        \/ \E m \in Messages : Receive(p, m)

Spec == Init /\ [][Next]_vars

====