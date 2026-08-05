---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

AllMessages ==
    [to : Proc, from : Proc, kind : {"alive"}]

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET AllMessages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {[to |-> q, from |-> p, kind |-> "alive"] : q \in Proc \ {p}}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \in Proc \ {p} /\ q \notin suspect[p] THEN @ + 1 ELSE @]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup
                    {q \in Proc : lastHeard[q] > timeout[p]]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |-> @ + 1]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p, msgs) ==
    /\ clock[p] % SendPoint # 0 /\ clock[p] % PredictPoint # 0
    /\ clock[p] < SendPoint /\ clock[p] < PredictPoint
    /\ \A q \in Proc \ {p} : timeout[p] <= SendPoint /\ timeout[p] <= PredictPoint
    /\ suspect' = [suspect EXCEPT ![p] = @ \ {q \in Proc : \E m \in msgs : m.to = p /\ m.from = q /\ m.kind = "alive"}]
    /\ lastHeard' = [q \in Proc |->
                        IF q \in {m.from : m \in msgs /\ m.to = p /\ m.kind = "alive"}
                        THEN 0
                        ELSE IF q \in suspect[p] THEN @ + 1
                        ELSE @]]
    /\ timeout' = [timeout EXCEPT ![p] = IF \E m \in msgs : m.to = p /\ m.kind = "alive" THEN @ + 1 ELSE @]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint
                         /\ \A q \in Proc \ {p} : clock[p] + 1 > timeout[p] THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED outbox

Next ==
    \/ \E p \in Proc : SendAlive(p) \/ Predict(p)
    \/ \E p \in Proc, msgs \in SUBSET Messages : Receive(p, msgs)

Spec ==
    /\ Init
    /\ [][Next]_vars

====