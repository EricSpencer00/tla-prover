---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ d0 \in Nat /\ d0 >= 1
       /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ SendPoint % PredictPoint # 0
       /\ PredictPoint % SendPoint # 0
       /\ SendPoint < Cardinality(Messages)
       /\ PredictPoint < Cardinality(Messages)

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

MaxClock == SendPoint + PredictPoint + 2

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> NATURAL]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q = p \/ lastHeard[q] >= timeout[p] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup
        {q \in Proc : q # p /\ lastHeard[q] > timeout[p]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q = p \/ lastHeard[q] >= timeout[p] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ \/ \E m \in outbox[p] :
        /\ m.from # p
        /\ lastHeard[m.from] > 0
        /\ lastHeard' = [lastHeard EXCEPT ![m.from] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![m.from] =
              IF m.from \in suspect[p] /\ @ < MaxClock THEN @ + 1 ELSE @]
     /\ ~ (\E m \in outbox[p] : TRUE)
     /\ lastHeard' = lastHeard
     /\ suspect' = suspect
     /\ timeout' = timeout
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > MaxClock THEN 0 ELSE @ + 1]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====