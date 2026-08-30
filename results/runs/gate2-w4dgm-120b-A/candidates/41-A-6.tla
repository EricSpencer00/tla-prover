---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* A process suspects another when last-heard has passed that other's timeout.
\* Send and predict are grid-locked by the two intervals never coinciding.
\* Adaptive timeout: a process's timeout grows when its own message is late.

VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

Me == CHOOSE p \in Proc : TRUE
Other(q) == {x \in Proc : x # q}
MaxT == 2

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> 0..MaxT]]
  /\ timeout \in [Proc -> [Proc -> 1..MaxT]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN d0 ELSE 1]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = [q \in Other(p) |-> [from |-> p, to |-> q]]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Other(p) |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Other(p) : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Other(p) |-> IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p, m) ==
  /\ m \notin outgoing[p]
  /\ m.to = p
  /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
  /\ suspect' = [suspect EXCEPT ![p] = @ \ {m.from}]
  /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p] /\ timeout[p][m.from] < MaxT
                                                    THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxT THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED <<outgoing>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc, m \in Messages : Receive(p, m)

Spec == Init /\ [][Next]_vars

\* Safety: every field stays inside its declared integer or set range.
TypeInvariant == TypeOK

====