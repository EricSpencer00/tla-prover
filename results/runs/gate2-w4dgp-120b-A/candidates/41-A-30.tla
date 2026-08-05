---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* An eventually perfect failure detector (Chandra & Toueg 1996) where each
\* process periodically sends alive messages, makes predictions about who
\* has crashed based on adaptive timeouts, and receives messages from
\* others. Send and predict are timed by a local clock; timeout intervals
\* adapt as messages arrive from previously-suspected processes. This is
\* the "correct-process" view: no process actually fails here.
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* A process sends an alive message to every other process.
Send(p) == { m \in Messages : m.to = p }

\* The send and predict intervals must never line up, so the two actions
\* cannot be scheduled at the same local clock value.
SendOK(k) == k % SendPoint = 0 /\ k % PredictPoint # 0
PredictOK(k) == k % PredictPoint = 0 /\ k % SendPoint # 0

TypeOK ==
  /\ \A p \in Proc : suspect[p] \subseteq Proc
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
  /\ \A p \in Proc : clock[p] \in Nat
  /\ \A p \in Proc : outbox[p] \subseteq Messages

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* Send an alive message to everyone else and tick the clock.
SendAction(p) ==
  /\ SendOK(clock[p])
  /\ outbox' = [outbox EXCEPT ![p] = Send(p)]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                 THEN @ + 1 ELSE @]
  /\ UNCHANGED <<suspect, timeout>>

\* Make a prediction: suspect everybody not heard from within the timeout.
PredictAction(p) ==
  /\ PredictOK(clock[p])
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup { q \in Proc : lastHeard[p][q] > timeout[p][q] }]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                 THEN @ + 1 ELSE @]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive incoming messages; reset counters and clear suspicions. If a
\* previously-suspected process sends a message, its timeout interval
\* grows, which is the adaptive part.
ReceiveAction(p, msgs) ==
  /\ ~SendOK(clock[p]) /\ ~PredictOK(clock[p])
  /\ \E from \in Proc : msgs = { m \in Messages : m.to = p /\ m.from = from }
  /\ \A from \in Proc : { m \in Messages : m.to = p /\ m.from = from } \subseteq msgs
  /\ suspect' = [suspect EXCEPT ![p] = @ \ { from \in Proc : { m \in Messages : m.from = from /\ m.to = p } \subseteq msgs }]
  /\ lastHeard' = [q \in Proc |-> IF { m \in Messages : m.from = q /\ m.to = p } \subseteq msgs THEN 0 ELSE @]
  /\ timeout' = [q \in Proc |-> IF { m \in Messages : m.from = q /\ m.to = p } \subseteq msgs /\ q \in suspect[p] THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ \A q \in Proc : @ + 1 > timeout[p][q] THEN 0 ELSE @ + 1]
  /\ UNCHANGED <<outbox>>

Next ==
  \/ \E p \in Proc : SendAction(p) \/ PredictAction(p)
  \/ \E p \in Proc, msgs \in SUBSET Messages : ReceiveAction(p, msgs)

Spec == Init /\ [][Next]_vars

====