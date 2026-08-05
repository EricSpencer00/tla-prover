---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* An eventually perfect failure detector: correct processes periodically send
\* alive messages and make failure predictions based on adaptive timeouts.
\* Send and predict steps are driven by a local clock that separates them so
\* they can never occur at the same instant.
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* For each process p: the processes p currently suspects as crashed, the
\* timeout interval p uses per process, a counter per process since p last
\* heard from it, a local clock, and the outgoing messages p wants to send.
VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

MsgType == [to: Proc, from: Proc, kind: {"alive"}]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* p sends an alive message to every other process at SendPoint (not at
\* PredictPoint), and ticks its lastHeard counters for still-timed-out procs.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF @[#] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

\* p makes a failure prediction at PredictPoint (not at SendPoint): it adds any
\* process from which it has not heard past that process's timeout interval.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF @[#] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<outbox, timeout>>

\* In all other clock values, p receives messages: an alive message from q
\* resets p's counter for q and removes q from p's suspicion set. If q was
\* suspected, its timeout interval is increased (the adaptive timeout).
ReceiveMsg(p) ==
  /\ ~ (clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~ (clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ \E m \in outbox[p] : m.kind = "alive" /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
                                              /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p] THEN @ + 1 ELSE @]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = m.from THEN 0 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > d0 THEN 0 ELSE @ + 1]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ ReceiveMsg(p)

Spec == Init /\ [][Next]_vars

\* Every process reliably runs within bounded local clock intervals and timeout
\* intervals: each process's clock stays within 0 and the largest of SendPoint,
\* PredictPoint, and the maximum of its timeout intervals.
TimeBound == \A p \in Proc :
               /\ clock[p] >= 0 /\ clock[p] <= Max({SendPoint, PredictPoint, d0})
               /\ \A q \in Proc : timeout[p][q] >= d0 /\ timeout[p][q] <= 2 * d0

TypeOK == /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
          /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
          /\ \A p \in Proc : suspect[p] \subseteq Proc
          /\ \A p \in Proc : outbox[p] \subseteq Messages
====