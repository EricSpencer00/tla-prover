---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, sendBuf

vars == <<suspect, timeout, lastHeard, clock, sendBuf>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ sendBuf \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ sendBuf = [p \in Proc |-> {}]

\* Alive messages are sent at every SendPoint tick, but never at a PredictPoint tick
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ sendBuf' = [sendBuf EXCEPT ![p] = {m \in Messages : m.to = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |-> IF q \in sendBuf[p] /\ lastHeard[q] < timeout[q]
                                   THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

\* Predictions (suspicion updates) happen at every PredictPoint tick, but never at a SendPoint tick
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[q] > timeout[q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |-> IF lastHeard[q] < timeout[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<timeout, sendBuf>>

\* Receiving is the rest of the tick budget, and is where timeouts are adapted upward
Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ lastHeard' = [q \in Proc |-> IF q \in sendBuf[p] THEN 0 ELSE lastHeard[q]]
  /\ suspect' = [q \in Proc |-> {p' \in suspect[q] : p' \notin sendBuf[q]}]
  /\ timeout' = [q \in Proc |-> IF q \in sendBuf[p] /\ q \in suspect[q] THEN timeout[q] + 1 ELSE timeout[q]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint /\ \A q \in Proc : clock[p] + 1 > timeout[q] THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED sendBuf

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====