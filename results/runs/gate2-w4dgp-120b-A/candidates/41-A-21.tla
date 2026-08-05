---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # PredictPoint

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

TimedOut(p, q) == lastHeard[p][q] > timeout[p][q]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = q /\ q \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |->
                       IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE @]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup {q \in Proc \ {p} : TimedOut(p, q)}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |->
                       IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE @]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0 /\ clock[p] % PredictPoint # 0
  /\ \E r \in {q \in Proc \ {p} : \E m \in outbox[q] : m.to = p} :
       /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {r}]
       /\ timeout' = [timeout EXCEPT ![p][r] = IF r \in suspicion[p] THEN @ + 1 ELSE @]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint
                 /\ clock[p] + 1 > PredictPoint
                 /\ \A q \in Proc \ {p} : clock[p] + 1 > timeout[p][q]
                 THEN 0 ELSE clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |->
                       IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE @]]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A p \in Proc, q \in Proc \ {p} : lastHeard[p][q] \in Nat /\ timeout[p][q] \in Nat
  /\ \A p \in Proc : suspicion[p] \subseteq Proc /\ outbox[p] \subseteq Messages

====