---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

NoSelf(p) == {q \in Proc : q # p}

\* Clock-based gating: Send and Predict never coincide by construction.
SendNow(p) == clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
PredictNow(p) == clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in NoSelf(p) |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in NoSelf(p) |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ SendNow(p)
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = # \in NoSelf(p)}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in NoSelf(p) |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

\* Timed out on a process: suspect it until an alive message is later received.
Predict(p) ==
    /\ PredictNow(p)
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in NoSelf(p) : lastHeard[p][q] >= timeout[p][q]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in NoSelf(p) |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<timeout, outbox>>

\* Receiving an alive message drops the suspect and may adapt the timeout.
Receive(p, msgs) ==
    /\ ~SendNow(p)
    /\ ~PredictNow(p)
    /\ clock[p] <= SendPoint
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q \in NoSelf(p) : \E m \in msgs : m.from = q}]
    /\ timeout' = [timeout EXCEPT ![p] = [q \in NoSelf(p) |-> IF \E m \in msgs : m.from = q /\ q \in suspect[p] THEN @ + 1 ELSE @]]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in NoSelf(p) |-> IF q \in {m.from : m \in msgs} THEN 0 ELSE @]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] < SendPoint /\ clock[p] < PredictPoint /\ \A q \in NoSelf(p) : clock[p] < timeout[p][q]
                            THEN clock[p] + 1 ELSE 0]
    /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ msgs]

Next ==
    \/ \E p \in Proc : SendAlive(p) \/ Predict(p)
    \/ \E p \in Proc, msgs \in \E m \in outbox[p] : {m} : Receive(p, msgs)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ \A p \in Proc : lastHeard[p] \in [NoSelf(p) -> Nat]
    /\ \A p \in Proc : timeout[p] \in [NoSelf(p) -> Nat]
    /\ \A p \in Proc : suspect[p] \subseteq Proc
    /\ \A p \in Proc : outbox[p] \subseteq Messages

====