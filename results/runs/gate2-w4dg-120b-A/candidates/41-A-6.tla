---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* A process is slow (its local clock drifts) but never fails, so the model
\* tracks per-process clocks and per-process suspicion lists.  Nothing
\* crashes; correctness lives in the adaptive timeouts.

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, heard, clock, outbox

vars == <<suspicion, timeout, heard, clock, outbox>>

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ heard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ heard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

MaxTimeout == Max([p \in Proc |-> timeout[p]])

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {q \in Proc : q # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ heard' = [q \in Proc |-> IF q = p \/ heard[q] < timeout[q] + 1 THEN 0 ELSE heard[q] + 1]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup {q \in Proc : q # p /\ heard[p] > timeout[q]}]
  /\ heard' = [q \in Proc |-> IF q = p \/ heard[q] < timeout[q] + 1 THEN 0 ELSE heard[q] + 1]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E r \in [From : Proc, To : Proc] :
        /\ r.To = p
        /\ r.From # p
        /\ ~ (r.From \in suspicion[p])
        /\ heard' = [heard EXCEPT ![r.From] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {r.From}]
        /\ timeout' = [timeout EXCEPT ![r.From] = IF r.From \in suspicion[p] THEN timeout[r.From] + 1 ELSE timeout[r.From]]
        /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {r}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxTimeout THEN 0 ELSE clock[p] + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====