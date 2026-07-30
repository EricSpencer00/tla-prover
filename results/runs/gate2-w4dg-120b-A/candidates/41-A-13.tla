---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* The system is an eventually perfect failure detector (Chandra-Toueg 1996)
\* in which each correct process periodically sends alive messages to
\* every other process.  A process predicts a crash for another process
\* only after not hearing from it for longer than that process's adaptive
\* timeout interval -- a timeout that can grow if a suspected process
\* keeps sending messages.  Send and predict events are driven by a
\* local clock with two non-conflicting intervals.

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

NoMsg == CHOOSE m \in Messages : TRUE

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p][q] = IF q \in outbox[p] THEN 0 ELSE IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ UNCHANGED <<suspicion, timeout>>

MakePrediction(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p][q] = IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] | q \in Proc]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

ReceiveMsg(p) ==
  /\ \E msgs \in SUBSET Messages :
       /\ \A m \in msgs : m.to = p
       /\ lastHeard' = [q \in Proc |-> IF \E m \in msgs : m.from = q THEN 0 ELSE lastHeard[p][q]]
       /\ suspicion' = [q \in Proc |-> IF \E m \in msgs : m.from = q THEN suspicion[p] \ {q} ELSE suspicion[p][q]]
       /\ timeout' = [q \in Proc |-> IF \E m \in msgs : m.from = q /\ q \in suspicion[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= SendPoint /\ clock[p] >= PredictPoint /\ \A q \in Proc : clock[p] >= timeout[p][q] THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : MakePrediction(p)
  \/ \E p \in Proc : ReceiveMsg(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

====