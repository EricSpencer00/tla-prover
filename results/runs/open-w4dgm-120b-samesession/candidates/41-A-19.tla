---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ SendPoint > 0
ASSUME PredictPoint \in Nat /\ PredictPoint > 0
ASSUME SendPoint # PredictPoint /\ SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0

\* Each process sends periodic alive messages, and separately makes
\* predictions about who has crashed.  The two schedules are kept apart
\* by the send/predict coprime-interval requirement.
\* An adaptive timeout interval governs when a missing alive message is
\* sufficient cause for suspicion.

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

MsgSpace == [src : Proc, dst : Proc]

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ outbox \in SUBSET MsgSpace

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = outbox \cup {[src |-> p, dst |-> q] : q \in Proc \ {p}}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in suspicion[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in suspicion[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ LET recv == {m \in outbox : m.dst = p} IN
       /\ suspicion' = [q \in Proc |-> IF q \in {m.src : m \in recv} THEN suspicion[p] \ {q} ELSE suspicion[p]]
       /\ lastHeard' = [q \in Proc |-> IF q \in {m.src : m \in recv} THEN 0 ELSE lastHeard[p][q]]
       /\ outbox' = outbox \ recv
       /\ timeout' = [q \in Proc |->
            IF q \in {m.src : m \in recv} /\ q \in suspicion[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]
       /\ clock' = IF clock[p] + 1 > 2 * (SendPoint + PredictPoint) + d0
                    THEN 0
                    ELSE clock[p] + 1

Next ==
  \/ \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====