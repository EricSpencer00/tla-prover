---- MODULE EPFailureDetector ----
EXTENDS Integers, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* A process suspects another only after not hearing from it longer than a
\* configurable timeout. Timeouts grow whenever a previously-crashed
\* (but now-alive) process manages to send a message through.
VARIABLES suspected, timeout, lastHeard, clock, pending

TypeOK ==
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ pending \in [Proc -> SUBSET Messages]

Init ==
    /\ suspected = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ pending = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = [pending EXCEPT ![p] = {m \in Messages : m.to = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [q \in Proc |->
            IF q \in suspected[p] /\ lastHeard[p] < timeout[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
    /\ UNCHANGED <<suspected, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \cup {q \in Proc : q # p /\ lastHeard[p] >= timeout[p]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [q \in Proc |->
            IF q \in suspected[p] /\ lastHeard[p] < timeout[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
    /\ UNCHANGED <<timeout, pending>>

Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ pending' = [pending EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] > 2 * SendPoint /\ clock[p] > timeout[p] THEN 0 ELSE clock[p] + 1]
    /\ lastHeard' = [q \in Proc |->
            IF \E m \in pending[p] : m.from = q /\ m.to = p
                THEN 0
                ELSE IF q \in suspected[p] /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
                    THEN lastHeard[p] + 1
                    ELSE lastHeard[p]]
    /\ suspected' = [suspected EXCEPT ![p] = suspected[p] \ {q \in Proc :
            \E m \in pending[p] : m.from = q /\ m.to = p}]
    /\ timeout' = [q \in Proc |->
            IF \E m \in pending[p] : m.from = q /\ m.to = p /\ q \in suspected[p]
                THEN timeout[p] + 1
                ELSE timeout[p]]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_<<suspected, timeout, lastHeard, clock, pending>>

====