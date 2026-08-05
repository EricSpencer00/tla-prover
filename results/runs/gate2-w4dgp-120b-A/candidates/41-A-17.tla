---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each partition is a participant in a bank interbank settlement network.  An
\* eventually perfect failure detector: a partition stops sending settlement
\* ticks (it is slow, not failed) and is eventually suspected -- never missed,
\* and the timeout bound is stretched while it is slow.
VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

Nxt(x) == (x % 4) + 1

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Sending is timed by the local clock and never coincides with a prediction.
SendAlive(p) ==
  /\ (clock[p] % SendPoint) = 0
  /\ (clock[p] % PredictPoint) # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % 8]
  /\ lastHeard' = [lastHeard EXCEPT
        ![p] = [q \in Proc \ {p} |-> IF lastHeard[p][q] >= timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<suspicion, timeout>>

\* A prediction is made from the same local clock, never at the same tick.
Predict(p) ==
  /\ (clock[p] % PredictPoint) = 0
  /\ (clock[p] % SendPoint) # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT
        ![p] = [q \in Proc \ {p} |-> IF lastHeard[p][q] >= timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
  /\ clock' = [clock EXCEPT ![p] = (clock[p] + 1) % 8]
  /\ UNCHANGED <<timeout, outbox>>

\* Receiving is the only way a suspicion is taken back.  A message from a
\* suspect is taken as evidence of slowness and the timeout is stretched.
Receive(p, msgs) ==
  /\ ~(clock[p] % SendPoint = 0 /\ (clock[p] % PredictPoint) # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ (clock[p] % SendPoint) # 0)
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc \ {p} |-> IF q \in {m.from : m \in msgs} THEN 0 ELSE lastHeard[p][q]]]
  /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q \in Proc \ {p} : q \in {m.from : m \in msgs}}]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc \ {p} |-> IF q \in {m.from : m \in msgs} /\ q \in suspicion[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = IF (clock[p] + 1) >= Nxt(Nxt(SendPoint)) /\ (clock[p] + 1) >= Nxt(Nxt(PredictPoint)) /\ (clock[p] + 1) >= Nxt(Nxt(d0)) THEN 0 ELSE (clock[p] + 1) % 8]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
  \E p \in Proc :
    \/ SendAlive(p) \/ Predict(p)
    \/ \E msgs \in {S \in Messages : \A m \in S : m.to = p}: Receive(p, msgs)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> 0..(Nxt(Nxt(d0))-1)]]
  /\ timeout \in [Proc -> [Proc -> 0..(Nxt(Nxt(d0))-1)]]
  /\ suspicion \in [Proc -> SUBSET (Proc \ {p})]
  /\ outbox \in [Proc -> SUBSET Messages]

====