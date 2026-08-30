---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspects, timeout, notHeard, clock, outbox

vars == <<suspects, timeout, notHeard, clock, outbox>>

TypeOK ==
  /\ suspects \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ notHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspects = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ notHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |->
        IF q \notin suspects[p] THEN @ ELSE notHeard[p][q] + 1]]
  /\ UNCHANGED <<suspects, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspects' = [suspects EXCEPT ![p] =
        @ \cup { q \in Proc : notHeard[p][q] > timeout[p][q] }]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ notHeard' = [notHeard EXCEPT ![p] = [q \in Proc |->
        IF q \notin suspects[p] /\ q # p
          THEN notHeard[p][q] + 1 ELSE notHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ suspects' = [suspects EXCEPT ![p] =
        @ \ { m.from : m \in outbox[p] /\ m.from \in suspects[p] }]
  /\ timeout' = [q \in Proc |->
        IF q \in {m.from : m \in outbox[p] /\ m.from \in suspects[p]}
          THEN [timeout[q] EXCEPT ![p] = @ + 1]
          ELSE timeout[q]]
  /\ notHeard' = [q \in Proc |->
        IF q = p THEN notHeard[p][q]
        ELSE IF \E m \in outbox[p] : m.from = q
          THEN 0
          ELSE notHeard[p][q]]
  /\ clock' = [clock EXCEPT ![p] =
        IF clock[p] > 2 * SendPoint + 2 * PredictPoint
          THEN 0
          ELSE clock[p] + 1]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====