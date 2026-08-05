---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Correct processes only: no fail/recover, only adaptive timeouts and clock-driven ops
VARIABLES suspect, timeout, lastHeard, clockValue, outbox

vars == <<suspect, timeout, lastHeard, clockValue, outbox>>

\* Fresh universe of messages, filtered by the controlling environment
SourceSet == {m \in Messages : m.from \in Proc /\ m.to \in Proc /\ m.from # m.to}

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ clockValue = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Send messages and tick last-heard counters; never fires at the predict interval
SendAlive(p) ==
  /\ clockValue[p] % SendPoint = 0
  /\ clockValue[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in SourceSet : m.from = p}]
  /\ clockValue' = [clockValue EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc \ {p} |->
        IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ UNCHANGED <<suspect, timeout>>

\* Re-evaluate who looks crashed, based on last-heard counters vs timeouts
Predict(p) ==
  /\ clockValue[p] % PredictPoint = 0
  /\ clockValue[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
        {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [q \in Proc \ {p} |->
        IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ clockValue' = [clockValue EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* Always open to receive; an alive message resets the suspect and the timer
Receive(p) ==
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clockValue' = [clockValue EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint
        /\ \A q \in Proc \ {p} : @ + 1 > timeout[p][q] THEN 0 ELSE @ + 1]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p]
        \ {[q \in Proc \ {p} : q \in {m.from : m \in outbox[p]}]}]
  /\ lastHeard' = [q \in Proc \ {p} |->
        IF q \in {m.from : m \in outbox[p]} THEN 0 ELSE lastHeard[p][q]]
  /\ timeout' = [q \in Proc \ {p} |->
        IF q \in {m.from : m \in outbox[p]} /\ q \in suspect[p] THEN timeout[p][q] + 1
        ELSE timeout[p][q]]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A p \in Proc : suspect[p] \subseteq Proc
  /\ \A p \in Proc : \A q \in Proc : timeout[p][q] \in Nat
  /\ \A p \in Proc : \A q \in Proc : lastHeard[p][q] \in Nat
  /\ \A p \in Proc : outbox[p] \subseteq SourceSet

====