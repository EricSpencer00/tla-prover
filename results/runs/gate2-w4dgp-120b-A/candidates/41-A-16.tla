---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastH, clock, outbox

vars == <<suspicion, timeout, lastH, clock, outbox>>

\* A process periodically sends alive messages to every other process (Send) and
\* periodically re-evaluates whom it suspects based on adaptive timeouts (Predict).
\* The two operations are kept temporally separate: neither send nor predict ever
\* fires at the same clock value, so suspicion changes only between message sends.

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ lastH = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

Send(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = q /\ q # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc \ {p} |->
                   IF q \in outbox[p] THEN 0
                   ELSE IF lastH[p][q] < timeout[p][q] THEN lastH[p][q] + 1
                   ELSE lastH[p][q]]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
                        {q \in Proc \ {p} : lastH[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc \ {p} |->
                   IF lastH[p][q] < timeout[p][q] THEN lastH[p][q] + 1
                   ELSE lastH[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q \in Proc \ {p} : [to |-> q] \in outbox[p]}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] > SendPoint /\ clock[p] > PredictPoint
                                 /\ \A q \in Proc \ {p} : clock[p] > timeout[p][q]
                                 THEN 0 ELSE clock[p] + 1]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc \ {p} |->
         IF [to |-> q] \in outbox[p] /\ q \in suspicion[p]
            /\ timeout[p][q] <= SendPoint
            /\ timeout[p][q] <= PredictPoint
         THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ lastH' = [lastH EXCEPT ![p] = [q \in Proc \ {p} |->
         IF [to |-> q] \in outbox[p] THEN 0
         ELSE IF lastH[p][q] < timeout[p][q] THEN lastH[p][q] + 1
         ELSE lastH[p][q]]]

Next ==
  \/ \E p \in Proc : Send(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastH \in [Proc -> [Proc \ {1} -> Nat]]
  /\ timeout \in [Proc -> [Proc \ {1} -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET Messages]

====