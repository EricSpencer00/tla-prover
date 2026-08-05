---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeoutInt, lastHeard, clock, outbox

vars == <<suspicion, timeoutInt, lastHeard, clock, outbox>>

NONE == "none"

TypeOK ==
  /\ lastHeard \in [Proc -> Nat]
  /\ timeoutInt \in [Proc -> Nat]
  /\ suspicion \subseteq Proc
  /\ outbox \subseteq Messages

Init ==
  /\ suspicion = {}
  /\ timeoutInt = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = 0
  /\ outbox = {}

\* Two intervals: sending alive messages and predicting crashes. They never
\* coincide because SendPoint and PredictPoint are constrained to be non-multiples
\* of each other, so send and predict actions are disjoint in time.
SendAlive ==
  /\ clock % SendPoint = 0
  /\ clock % PredictPoint # 0
  /\ outbox' = {m \in Messages : m.dest = NONE}
  /\ clock' = clock + 1
  /\ lastHeard' = [p \in Proc |->
        IF lastHeard[p] + 1 < timeoutInt[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED <<suspicion, timeoutInt>>

Predict ==
  /\ clock % PredictPoint = 0
  /\ clock % SendPoint # 0
  /\ suspicion' = suspicion \cup {p \in Proc : lastHeard[p] > timeoutInt[p]}
  /\ clock' = clock + 1
  /\ lastHeard' = [p \in Proc |->
        IF lastHeard[p] + 1 < timeoutInt[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED <<timeoutInt, outbox>>

\* Time-bounded: the clock is reset once it clears every threshold.
ClockReset ==
  /\ clock > SendPoint
  /\ clock > PredictPoint
  /\ \A p \in Proc : clock > timeoutInt[p]
  /\ clock' = 0
  /\ UNCHANGED <<suspicion, timeoutInt, lastHeard, outbox>>

\* Receive a message from some process out of the shared Messages set. Because
\* messages are drawn from a global set, the controller decides which process's
\* message is delivered in each transition, so a crashed process's
\* message may be delayed arbitrarily but is never dropped.
Receive(p) ==
  /\ p \notin suspicion
  /\ \E m \in outbox : m.dest = p
  /\ outbox' = {m \in outbox : m.dest # p}
  /\ suspicion' = suspicion \ {p}
  /\ lastHeard' = [lastHeard EXCEPT ![p] = 0]
  /\ timeoutInt' = [timeoutInt EXCEPT ![p] = IF p \in suspicion
                        THEN timeoutInt[p] + 1 ELSE timeoutInt[p]]
  /\ clock' = clock + 1

Next ==
  \/ SendAlive
  \/ Predict
  \/ ClockReset
  \/ (\E p \in Proc : Receive(p))

Spec == Init /\ [][Next]_vars

====