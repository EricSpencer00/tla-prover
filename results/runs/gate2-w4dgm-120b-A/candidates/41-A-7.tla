---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspect, timeout, lastHeard, pending

vars == <<clock, suspect, timeout, lastHeard, pending>>

MaxClock == SendPoint + PredictPoint + d0

\* Every process acts on its own local clock; send and predict are timed so
\* they never happen in the same transition.
TypeOK ==
  /\ clock \in [Proc -> 0..MaxClock]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> SUBSET Proc -> 0..d0]
  /\ lastHeard \in [Proc -> SUBSET Proc -> 0..d0]
  /\ pending \in [Proc -> SUBSET Messages]

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ pending = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ pending' = [pending EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in pending[p] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> @ + 1]]
  /\ UNCHANGED <<timeout, pending>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in pending[p]:
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
       /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p] THEN (@ + 1) % (d0 + 1) ELSE @]
  /\ pending' = [pending EXCEPT ![p] = @ \ {m \in pending[p] : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = IF @ = MaxClock THEN 0 ELSE @ + 1]

Next ==
  \/ \E p \in Proc: SendAlive(p)
  \/ \E p \in Proc: Predict(p)
  \/ \E p \in Proc: Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(\E p \in Proc: SendAlive(p))
  /\ WF_vars(\E p \in Proc: Predict(p))

\* A correct process is only ever suspected long after it has truly gone
\* quiet, once the adaptive timeout has caught up.
SuspectSound == \A p \in Proc: (suspect[p] # {}) ~> (suspect[p] = {})

====