---- MODULE EPFailureDetector ----
\* Eventual perfection: correct processes in a failure detector that times out
\* a process only after it has stopped hearing from it; the local clock per
\* process separates sending alive messages from making predictions.
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outbox
vars == <<suspicion, timeout, lastHeard, clock, outbox>>

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.dest = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF clock[p] >= timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] =
        suspicion[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF clock[p] >= timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<timeout, outbox>>

Reset(p) ==
  /\ \E m \in outbox[p] : TRUE
  /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m \in outbox[p] : m.dest = p}]
  /\ UNCHANGED <<suspicion, timeout, lastHeard, clock>>

Receive(p) ==
  /\ \A m \in outbox[p] : m.dest = p
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0 ELSE 0]]
  /\ suspicion' = [suspicion EXCEPT ![p] = {q \in suspicion[p] : q # p}]
  /\ timeout' = [timeout EXCEPT ![p][p] = IF p \in suspicion[p] THEN timeout[p][p] + 1 ELSE timeout[p][p]]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : Reset(p)

Spec == Init /\ [][Next]_vars

====