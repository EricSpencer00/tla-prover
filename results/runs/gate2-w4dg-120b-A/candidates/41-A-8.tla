---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # PredictPoint

VARIABLES suspicion, timeout, lastHeard, tick, outbox

vars == <<suspicion, timeout, lastHeard, tick, outbox>>

\* A process sends alive messages at every multiple of SendPoint and predicts
\* failures at every multiple of PredictPoint; the two intervals never
\* coincide, so sending and predicting are separate steps.

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \subseteq (Proc \X Proc)
  /\ outbox \subseteq Messages

Init ==
  /\ suspicion = {}
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ tick = [p \in Proc |-> 0]
  /\ outbox = {}

SendAlive(p) ==
  /\ tick[p] % SendPoint = 0
  /\ tick[p] % PredictPoint # 0
  /\ outbox' = {m \in Messages : m.from = p /\ m.to \in Proc}
  /\ tick' = [tick EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ tick[p] % PredictPoint = 0
  /\ tick[p] % SendPoint # 0
  /\ suspicion' = {r \in suspicion : r[1] = p} \cup
        {<<p, q>> \in Proc \X Proc :
           lastHeard[p][q] > timeout[p][q]}
  /\ tick' = [tick EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<timeout, outbox>>

\* The receive step resets the last-heard counter for a process from which an
\* alive message is received and removes it from the suspicion set. Processing
\* a message from a process that had been timed out on raises its timeout, an
\* adaptive mechanism that eventually lets correct processes stop being
\* suspected.
Receive(p) ==
  /\ tick' = [tick EXCEPT ![p] =
        IF tick[p] + 1 > SendPoint /\ tick[p] + 1 > PredictPoint
            /\ \A q \in Proc : tick[p] + 1 > timeout[p][q]
        THEN 0 ELSE tick[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF \E m \in outbox : m.to = p /\ m.from = q
                         THEN 0 ELSE @]]
  /\ suspicion' = {r \in suspicion : r[1] = p}
        \cup
        {<<p, q>> \in Proc \X Proc : \E m \in outbox : m.to = p /\ m.from = q}
  /\ timeout' = [q \in Proc |-> IF \E m \in outbox : m.to = p /\ m.from = q
                                   /\ <<p, q>> \in suspicion
                                   THEN timeout[p][q] + 1 ELSE timeout[p][q]]
  /\ UNCHANGED outbox

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====