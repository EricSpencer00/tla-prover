---- MODULE EPFailureDetector ----
EXTENDS Integers, FiniteSets

\* System modelled on the eventually perfect failure detector of Chandra & Toueg, 1996.
\* Each process has a local clock, suspicion list, adaptive timeouts, and last-heard counters.
\* Send and predict steps never overlap, because the send and predict points are taken to
\* be distinct modulo the clock range.

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

MaxClk == d0 + 2

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

\* Send alive messages to every other process, at the next send point.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.dst \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |-> IF q # p /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

\* Predict based on last-heard counters surpassing the timeout interval.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
                                   {q \in Proc \ {p} : lastHeard[q] > timeout[p]}]
  /\ lastHeard' = [q \in Proc |-> IF q # p /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive in-flight messages; adaptive timeout rises upon trusting a suspect.
Receive(p) ==
  /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ suspect' = [q \in Proc |-> IF lastHeard[p] > timeout[p] /\ p \notin suspect[q]
                                    THEN suspect[q] \ {p} ELSE suspect[q]]
  /\ timeout' = [q \in Proc |-> IF lastHeard[p] > timeout[p] /\ p \in suspect[q]
                                  THEN timeout[p] + 1 ELSE timeout[p]]
  /\ lastHeard' = [q \in Proc |-> IF q # p /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxClk THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED outbox

Next ==
  \E p \in Proc :
    \/ SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====