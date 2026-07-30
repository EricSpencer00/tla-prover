---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* An eventually perfect failure detector: processes periodically send
\* "alive" messages and periodically predict who has crashed; predictions
\* are based on per-process adaptive timeout intervals. The send and
\* predict operations are timed on the local clock and are arranged to
\* never coincide by constraining the send/predict intervals to be
\* non-multiples of each other. This is a faithful mechanization of the
\* Chandra & Toueg framework in which a correct process is eventually no
\* longer suspected once it has truly recovered.

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint > 0 /\ PredictPoint > 0 /\ SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0
ASSUME d0 > 0

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* sent(p) = every other process that p wants to send an alive message to.
sent(p) == { m \in Messages : m.from = p }

\* recv(p) = every other process that has sent an alive message to p.
recv(p) == { m \in Messages : m.to = p }

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \subseteq Messages

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

Send(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = outbox \cup sent(p)
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF q \in suspect[p] THEN @ ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup
        { q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q] }]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> lastHeard[p][q] + 1]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \ { q \in suspect[p] : q \in recv(p) }]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in recv(p) THEN 0 ELSE @]]
  /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |-> IF q \in recv(p) /\ q \in suspect[p] THEN timeout[p][q] + 1 ELSE @]]
  /\ outbox' = outbox \ recv(p)
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= SendPoint /\ clock[p] >= PredictPoint /\ \A q \in Proc : clock[p] >= timeout[p][q] THEN 0 ELSE clock[p] + 1]

Next ==
  \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====