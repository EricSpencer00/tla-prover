---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process tracks a suspicion set, per-process timeout intervals, a
\* last-heard counter per other process, a local clock, and its outgoing
\* messages.  Send and predict actions are driven by the local clock and
\* never fire at the same clock value (the two intervals are co-prime).
VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
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
        IF q \in suspect[p] /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [p \in Proc |->
        IF p = p
          THEN suspect[p] \cup {q \in Proc : lastHeard[q] > timeout[p]}
          ELSE suspect[p]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \in suspect[p] /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ clock[p] # 0
  /\ suspect' = [p \in Proc |->
        {q \in suspect[p] : ~(\E m \in outbox[p] : m.from = q)}]
  /\ lastHeard' = [q \in Proc |->
        IF \E m \in outbox[p] : m.from = q THEN 0 ELSE lastHeard[q]]
  /\ timeout' = [p \in Proc |->
        IF \E m \in outbox[p] : m.from \in suspect[p] THEN timeout[p] + 1 ELSE timeout[p]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] > 2 * SendPoint THEN 0 ELSE @ + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====