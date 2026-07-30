---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES
    suspect, timeout, lastHeard, clock, outbox

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

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] THEN @ + 1 ELSE @]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[q] > timeout[q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] THEN @ + 1 ELSE @]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \ {q \in Proc : \E m \in outbox[p] : m.to = q}]
    /\ timeout' = [q \in Proc |-> IF q \in suspect[p] /\ \E m \in outbox[p] : m.to = q THEN timeout[q] + 1 ELSE timeout[q]]
    /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > d0 THEN 0 ELSE @ + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] /\ \E m \in outbox[p] : m.to = q THEN 0 ELSE @]
    /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====