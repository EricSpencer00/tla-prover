---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* A correct process sends alive messages to all others at every multiple of
\* SendPoint, and separately makes predictions about who has crashed at every
\* multiple of PredictPoint.  The two intervals are constrained to never
\* coincide, so sending and predicting are always distinct steps.

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF @[#q] < timeout[p][q] THEN @[#q] + 1 ELSE @[#q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF @[#q] < timeout[p][q] THEN @[#q] + 1 ELSE @[#q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in outbox[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.to] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.to}]
       /\ timeout' = [timeout EXCEPT ![p][m.to] = IF m.to \in suspect[p] THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > timeout[p][p] THEN 0 ELSE @ + 1]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A p \in Proc : \A q \in Proc : lastHeard[p][q] \in Nat /\ timeout[p][q] \in Nat
  /\ \A p \in Proc : suspect[p] \subseteq Proc
  /\ \A p \in Proc : outbox[p] \subseteq Messages

====