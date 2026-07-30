---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in (Nat \ {0})
ASSUME PredictPoint \in (Nat \ {0})
\* Send and predict are never simultaneous, which is what keeps the two
\* steps separate; their being multiples of each other would collapse them.
ASSUME SendPoint % PredictPoint # 0
ASSUME PredictPoint % SendPoint # 0

VARIABLES suspect, deadline, lastHeard, clock, outbox

vars == <<suspect, deadline, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ deadline \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ deadline = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Send alive messages at each SendPoint tick; always raises the local clock.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] \/ clock[p] > deadline[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, deadline>>

\* Predict at each PredictPoint tick; always raises the local clock.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[q] > deadline[q]}]
  /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] \/ clock[p] > deadline[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<deadline, outbox>>

\* Normal ticks: receive whatever is pending, adapt timeouts for recovered processes.
Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \ {q \in Proc : \E m \in outbox[p] : m.to = q}]
  /\ lastHeard' = [q \in Proc |-> IF \E m \in outbox[p] : m.to = q THEN 0 ELSE lastHeard[q]]
  /\ deadline' = [q \in Proc |-> IF \E m \in outbox[p] : m.to = q /\ q \in suspect[p] THEN @ + 1 ELSE @]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = IF clock[p] >= SendPoint + PredictPoint + deadline[p] THEN [clock EXCEPT ![p] = 0]
              ELSE [clock EXCEPT ![p] = @ + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====