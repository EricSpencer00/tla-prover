---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process tracks a suspicion set, a per-peer timeout interval, a
\* per-peer last-heard counter, a local clock, and its outgoing messages.
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

\* Send alive messages to every other process at a send tick.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \in suspect[p] /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

\* Predict crashes at a predict tick, based on adaptive timeouts.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
        {q \in Proc : q # p /\ lastHeard[q] > timeout[p]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \in suspect[p] /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive messages; adaptive timeout grows when a suspected process sends.
Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in outbox[p] :
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![p] =
              IF m.from \in suspect[p] THEN timeout[p] + 1 ELSE timeout[p]]
        /\ lastHeard' = [lastHeard EXCEPT ![m.from] = 0]
  /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

\* Clock and counters reset once all thresholds are passed, keeping the domain finite.
Reset(p) ==
  /\ clock[p] > SendPoint
  /\ clock[p] > PredictPoint
  /\ \A q \in Proc : lastHeard[q] > timeout[p]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ lastHeard' = [q \in Proc |-> 0]
  /\ UNCHANGED <<suspect, timeout, outbox>>

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p) \/ Reset(p)

Spec == Init /\ [][Next]_vars

====