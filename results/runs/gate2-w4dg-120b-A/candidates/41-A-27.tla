---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>


TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.sender = p /\ m.receiver \in Proc}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                      IF q \notin Proc THEN @
                      ELSE IF q \notin Proc THEN @
                      ELSE IF q \in Proc /\ clock[p] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                      IF q \notin Proc THEN @
                      ELSE IF q \in Proc /\ clock[p] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q \in Proc : \E m \in outbox[q] : m.receiver = p}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                      IF \E m \in outbox[q] : m.receiver = p THEN 0 ELSE @]]
  /\ timeout' = [timeout EXCEPT ![p][q] =
                    IF \E m \in outbox[q] : m.receiver = p /\ q \in suspicion[p] THEN timeout[p][q] + 1 ELSE @]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] < SendPoint /\ clock[p] < PredictPoint /\ \A r \in Proc : clock[p] < timeout[p][r]
                                        THEN clock[p] + 1
                                        ELSE 0]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars

====