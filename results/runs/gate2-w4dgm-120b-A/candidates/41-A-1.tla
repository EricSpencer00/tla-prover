---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ SendPoint # PredictPoint
       /\ SendPoint % PredictPoint # 0
       /\ PredictPoint % SendPoint # 0
       /\ d0 \in Nat /\ d0 > 0

VARIABLES suspect, timeout, lastheard, clock, outbound

vars == <<suspect, timeout, lastheard, clock, outbound>>

\* Deadline is the largest timeout any process is currently tracking; it
\* bounds when the local clock may safely reset.
Deadline == CHOOSE m \in Nat :
               /\ (\A q \in Proc: \A r \in Proc \ {q}: timeout[r][q] <= m)
               /\ (\A k \in Nat: (\A q \in Proc: \A r \in Proc \ {q}: timeout[r][q] <= k) => m <= k)

TypeOK ==
  /\ lastheard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ clock \in [Proc -> Nat]
  /\ outbound \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [q \in Proc |-> {}]
  /\ timeout = [q \in Proc |-> [r \in Proc |-> IF r = q THEN 0 ELSE d0]]
  /\ lastheard = [q \in Proc |-> [r \in Proc |-> 0]]
  /\ clock = [q \in Proc |-> 0]
  /\ outbound = [q \in Proc |-> {}]

SendAlive(q) ==
  /\ clock[q] % SendPoint = 0
  /\ clock[q] % PredictPoint # 0
  /\ outbound' = [outbound EXCEPT ![q] = {m \in Messages : m.dest \in Proc \ {q}}]
  /\ clock' = [clock EXCEPT ![q] = @ + 1]
  /\ lastheard' = [lastheard EXCEPT ![q] = [r \in Proc |-> IF r \in suspect[q] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(q) ==
  /\ clock[q] % PredictPoint = 0
  /\ clock[q] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![q] = @ \cup
                   {r \in Proc \ {q}: lastheard[q][r] > timeout[q][r]}]
  /\ clock' = [clock EXCEPT ![q] = @ + 1]
  /\ lastheard' = [lastheard EXCEPT ![q] = [r \in Proc |-> IF r \in suspect[q] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<timeout, outbound>>

\* The delivery step is where a timeout count gets reset, and where an
\* adaptive timeout is raised when a suspect's message finally arrives.
Receive(q, msgs) ==
  /\ clock[q] % SendPoint # 0
  /\ clock[q] % PredictPoint # 0
  /\ clock[q] <= Deadline
  /\ outbound' = [outbound EXCEPT ![q] = outbound[q] \ msgs]
  /\ clock' = [clock EXCEPT ![q] = IF @ + 1 > Deadline THEN 0 ELSE @ + 1]
  /\ lastheard' = [lastheard EXCEPT ![q] =
                     [r \in Proc |-> IF \E m \in msgs: m.dest = r THEN 0 ELSE @]]
  /\ suspect' = [suspect EXCEPT ![q] =
                   {r \in suspect[q] : ~(\E m \in msgs: m.dest = r)}]
  /\ timeout' = [timeout EXCEPT ![q] =
                   [r \in Proc |-> IF \E m \in msgs: m.dest = r /\ r \in suspect[q]
                                   THEN @ + 1 ELSE @]]

Next ==
  \E q \in Proc:
    \/ SendAlive(q)
    \/ Predict(q)
    \/ \E msgs \in SUBSET Messages: Receive(q, msgs)

Spec == Init /\ [][Next]_vars

====