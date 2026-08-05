---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* An eventually perfect failure detector: each correct process predicts which
\* others have crashed based on a per-peer adaptive timeout. Two periodic
\* actions (sending alive messages, making predictions) are kept apart by
\* the send/predict interval constraint.

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

NoSend == [to |-> "none", kind |-> "none"]

VARIABLES suspicion, timeout, lastHeard, clock, toSend

vars == << suspicion, timeout, lastHeard, clock, toSend >>

Bump(n, m) == IF n < m THEN n + 1 ELSE n

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ toSend \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ toSend = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ toSend' = [toSend EXCEPT ![p] = { [to |-> q, kind |-> "alive"] : q \in Proc \ {p} }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = IF lastHeard[p] < timeout[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup {q \in Proc \ {p} : lastHeard[p] > timeout[p]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = IF lastHeard[p] < timeout[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED << timeout, toSend >>

Receive(p) ==
  /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q \in Proc \ {p} : \E m \in toSend[q] : m.to = p /\ m.kind = "alive"}]
  /\ timeout' = [timeout EXCEPT ![p] = IF \E q \in Proc \ {p} : \E m \in toSend[q] : m.to = p /\ m.kind = "alive" /\ q \in suspicion[p] THEN Bump(timeout[p], 3) ELSE timeout[p]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] > 3 /\ clock[p] > timeout[p] + 1 THEN 0 ELSE clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = 0]
  /\ UNCHANGED << toSend >>

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Spec == Init /\ [][Next]_vars

====