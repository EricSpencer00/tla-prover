---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspect, timeout, lastHeard, outbox

vars == <<clock, suspect, timeout, lastHeard, outbox>>

\* adaptive timeout: correct processes are never permanently suspected, only delayed

TypeOK ==
  /\ \A p \in Proc :
       /\ suspect[p] \subseteq Proc
       /\ timeout[p] \in [Proc -> Nat]
       /\ lastHeard[p] \in [Proc -> Nat]
       /\ clock[p] \in Nat
       /\ outbox[p] \subseteq Messages

Init ==
  /\ \A p \in Proc :
       /\ suspect[p] = {}
       /\ timeout[p] = [q \in Proc |-> d0]
       /\ lastHeard[p] = [q \in Proc |-> 0]
       /\ clock[p] = 0
       /\ outbox[p] = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox[p]' = {m \in Messages : m.from = p}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ UNCHANGED <<suspect, timeout, outbox>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |-> lastHeard[p][q] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ \E m \in outbox[p] :
       /\ \E q \in Proc : m.from = q
          /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
          /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q}]
          /\ timeout' = [timeout EXCEPT ![p][q] = IF q \in suspect[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > Max({SendPoint, PredictPoint} \cup {timeout[p][q] : q \in Proc}) THEN 0 ELSE clock[p] + 1]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====