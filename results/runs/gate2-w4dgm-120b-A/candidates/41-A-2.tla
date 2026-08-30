---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ SendPoint % PredictPoint # 0
       /\ PredictPoint % SendPoint # 0

VARIABLES suspicion, timeout, lastHeard, clockP, outbox

vars == <<suspicion, timeout, lastHeard, clockP, outbox>>

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clockP = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clockP[p] % SendPoint = 0
  /\ clockP[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.sender = q /\ m.dest = p /\ q # p}]
  /\ clockP' = [clockP EXCEPT ![p] = clockP[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [r \in Proc |->
                       IF r \in suspicion[p] /\ lastHeard[p][r] < timeout[p][r]
                       THEN lastHeard[p][r] + 1 ELSE lastHeard[p][r]]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clockP[p] % PredictPoint = 0
  /\ clockP[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] =
                     @ \cup {r \in Proc : lastHeard[p][r] > timeout[p][r]}]
  /\ clockP' = [clockP EXCEPT ![p] = clockP[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [r \in Proc |-> IF
                       r \in suspicion[p] /\ lastHeard[p][r] < timeout[p][r]
                       THEN lastHeard[p][r] + 1 ELSE lastHeard[p][r]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clockP[p] % SendPoint # 0
  /\ clockP[p] % PredictPoint # 0
  /\ clockP[p] <= 2 * SendPoint
  /\ \E m \in outbox[p] : m.dest = p
  /\ \E q \in Proc :
       /\ q # p
       /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
       /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {q}]
       /\ timeout' = [timeout EXCEPT ![p][q] =
                        IF q \in suspicion[p] THEN @ + 1 ELSE @]
  /\ clockP' = [clockP EXCEPT ![p] = IF clockP[p] = 2 * SendPoint
                                            THEN 0 ELSE clockP[p] + 1]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====