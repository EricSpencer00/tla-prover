---- MODULE EPFailureDetector ----
EXTENDS Integers, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |->
                IF q = p THEN lastHeard[p][q]
                ELSE IF lastHeard[p][q] < timeout[p][q]
                     THEN lastHeard[p][q] + 1
                     ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |->
                IF lastHeard[p][q] < timeout[p][q]
                THEN lastHeard[p][q] + 1
                ELSE lastHeard[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p, m) ==
    /\ m \in outbox[p]
    /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m}]
    /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
    /\ timeout' = [timeout EXCEPT ![p][m.from] = timeout[p][m.from] + 1]
    /\ UNCHANGED clock

Tick(p) ==
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |->
                IF lastHeard[p][q] < timeout[p][q]
                THEN lastHeard[p][q] + 1
                ELSE lastHeard[p][q]]]
    /\ clock' = [clock EXCEPT ![p] =
            IF clock[p] >= SendPoint /\ clock[p] >= PredictPoint / \A q \in Proc : clock[p] >= timeout[p][q]
            THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED <<suspect, timeout, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc, m \in Messages : Receive(p, m)
    \/ \E p \in Proc : Tick(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Messages]

====