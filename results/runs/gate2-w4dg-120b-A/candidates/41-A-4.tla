---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

MaxVal(x) == IF x = {} THEN 0 ELSE LET f[S \in SUBSET Nat] ==
   IF S = {} THEN 0 ELSE LET m == CHOOSE y \in S : \A z \in S : y >= z
   IN m
  IN f[{timeout[p][q] : p \in Proc, q \in Proc, p # q} \cup {1}]

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspect \subseteq Proc
  /\ outbox \subseteq Messages
  /\ clock \in [Proc -> Nat]

Init ==
  /\ suspect = {}
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [p \in Proc |-> {m \in Messages : m.sender = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = suspect \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ suspect' = {q \in suspect : outbox[p] = {} \/ outbox[p].sender # q}
  /\ timeout' = [q \in Proc |->
        IF outbox[p] # {} /\ outbox[p].sender = q /\ outbox[p].msg = "alive"
        THEN timeout[p][q] + 1 ELSE timeout[p][q]]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF outbox[p] # {} /\ outbox[p].sender = q THEN 0 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT
        ![p] = IF (clock[p] + 1) >= SendPoint /\ (clock[p] + 1) >= PredictPoint
                 /\ (clock[p] + 1) >= MaxVal(lastHeard[p])
                 THEN 0 ELSE clock[p] + 1]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====