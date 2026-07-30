---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,
  d0,
  SendPoint,
  PredictPoint,
  Messages

\* State: each process's suspicion set, per-process timeout intervals, per-process
\* last-heard counter, local clock, and set of outgoing messages.
VARIABLES suspect, timeout, lastHeard, clock, outbox

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
  /\ outbox' = [outbox EXCEPT ![p] =
        {m \in Messages : m.who = p /\ m.to \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
        suspect[p] \cup {q \in Proc : lastHeard[q] > timeout[q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E M \in outbox[p] :
        suspect' = [suspect EXCEPT ![p] = suspect[p] \ {M.to}]
        /\ timeout' = [timeout EXCEPT ![M.to] =
            IF M.to \in suspect[p] THEN timeout[M.to] + 1 ELSE timeout[M.to]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > 3 + d0 THEN 0 ELSE clock[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_<<suspect, timeout, lastHeard, clock, outbox>>

\* The full integrity suite: last-heard and timeout are natural numbers; suspicion
\* sets are subsets of the process set; outboxes are subsets of the message type.
TypeOK == TypeOK
====