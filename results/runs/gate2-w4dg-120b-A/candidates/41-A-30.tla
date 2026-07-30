---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint > 0 /\ PredictPoint > 0
ASSUME SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0

VARIABLES clock, suspect, lastHeard, timeout, outbox

vars == <<clock, suspect, lastHeard, timeout, outbox>>

Idle(p) == \A m \in outbox : m.sender # p

TypeOK ==
  /\ \A p \in Proc : suspect[p] \subseteq Proc
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
  /\ \A p \in Proc : clock[p] \in Nat
  /\ \A p \in Proc : outbox[p] \subseteq Messages

Init ==
  /\ \A p \in Proc :
       /\ suspect[p] = {}
       /\ timeout[p] = [q \in Proc |-> d0]
       /\ lastHeard[p] = [q \in Proc |-> 0]
       /\ clock[p] = 0
       /\ outbox[p] = {}

AdvanceClock(p) ==
  /\ clock[p] < SendPoint
  /\ clock[p] < PredictPoint
  /\ \A q \in Proc : clock[p] < timeout[p][q]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<suspect, lastHeard, timeout, outbox>>

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {Messages[(p, q)] : q \in Proc \ {p}}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                       IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<suspect, timeout>>

MakePrediction(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                       IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ \A m \in outbox[p] : m.recipient = p
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                       IF \E m \in outbox[p] : m.sender = q THEN 0 ELSE lastHeard[p][q]]]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q \in Proc : \E m \in outbox[p] : m.sender = q}]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |->
                       IF \E m \in outbox[p] : m.sender = q /\ q \in suspect[p]
                       THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = 0]

Next == \E p \in Proc : SendAlive(p) \/ MakePrediction(p) \/ Receive(p) \/ AdvanceClock(p)

Spec == Init /\ [][Next]_vars

====