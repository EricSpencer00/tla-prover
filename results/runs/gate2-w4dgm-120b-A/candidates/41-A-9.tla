---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspect, timeout, lastHeard, outbox

TypeOK ==
  /\ clock \in [Proc -> Nat]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p, m) ==
  /\ m \in outbox[p]
  /\ outbox' = [outbox EXCEPT ![p] = @ \ {m}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = m.from THEN 0 ELSE @]]
  /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
  /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p] THEN @ + 1 ELSE @]
  /\ UNCHANGED clock

ResetClock(p) ==
  /\ clock[p] >= SendPoint * PredictPoint
  /\ \A q \in Proc : clock[p] < timeout[p][q]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc, m \in Messages : Receive(p, m)
  \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_<<clock, suspect, timeout, lastHeard, outbox>>

====