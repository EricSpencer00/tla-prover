---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ SendPoint >= 1
ASSUME PredictPoint \in Nat /\ PredictPoint >= 1
ASSUME SendPoint # PredictPoint

VARIABLES suspicion, timeout, noHear, clock, outbox

vars == <<suspicion, timeout, noHear, clock, outbox>>

\* noHear[p][q] is how long p has gone without hearing an alive message from q
TypeOK ==
  /\ noHear \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ noHear = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Alive messages are emitted toward every other process, not just one
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = p /\ m.from \in Proc /\ m.from # p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ noHear' = [q \in Proc |->
        [r \in Proc |->
          IF r = p /\ noHear[q][r] < timeout[q][r] THEN noHear[q][r] + 1
          ELSE noHear[q][r]]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [q \in Proc |->
        [r \in Proc |->
          IF r \in suspicion[q] \/ (r # q /\ noHear[q][r] > timeout[q][r])
          THEN r ELSE suspicion[q][r]]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ noHear' = [q \in Proc |->
        [r \in Proc |->
          IF r = p /\ noHear[q][r] < timeout[q][r] THEN noHear[q][r] + 1
          ELSE noHear[q][r]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in outbox[p] :
        /\ noHear' = [noHear EXCEPT ![p][m.from] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {m.from}]
        /\ timeout' = [q \in Proc |->
              [r \in Proc |->
                IF r = m.from /\ q = p /\ r \in suspicion[q] /\ noHear[q][r] > timeout[q][r]
                THEN timeout[q][r] + 1 ELSE timeout[q][r]]]
  /\ outbox' = [outbox EXCEPT ![p] = @ \ {m \in outbox[p] : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]

\* The local clock is reset once it has passed everything; this keeps the
\* shared clock domain finite without ever skipping a send or predict step
ResetClock(p) ==
  /\ clock[p] > SendPoint
  /\ clock[p] >= PredictPoint
  /\ \A q \in Proc : \A r \in Proc : clock[p] > timeout[q][r]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspicion, timeout, noHear, outbox>>

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p) \/ ResetClock(p)

Spec == Init /\ [][Next]_vars

====