---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* This spec implements the correct-process side of an eventually perfect
\* failure detector (Chandra-Toueg). Each process sends alive messages and
\* periodically revises its suspicion set; the timeout interval is
\* adaptive and can grow when a previously-suspected process finally
\* responds.

VARIABLES suspect, timeout, waited, clock, outbox

vars == <<suspect, timeout, waited, clock, outbox>>

Except(P, q) == {x \in P : x # q}
Idle(p) == \A q \in Proc : q # p => ~ <<p, q>> \in outbox

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ waited = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = {}

\* Send an alive message to every other process; this happens only on
\* multiples of SendPoint (and never on a PredictPoint multiple, by
\* construction of the intervals).
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = outbox \cup {<<p, q>> : q \in Except(Proc, p)}
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ waited' = [waited EXCEPT ![p] = [q \in Proc |-> IF q # p /\ waited[p][q] < timeout[p][q] THEN waited[p][q] + 1 ELSE waited[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Except(Proc, p) : waited[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ waited' = [waited EXCEPT ![p] = [q \in Proc |-> IF q # p /\ waited[p][q] < timeout[p][q] THEN waited[p][q] + 1 ELSE waited[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

\* Receive incoming messages. An alive message clears the waiting timer
\* and removes the sender from the suspicion set; receiving from a
\* currently-suspected process grows its timeout.
Receive(p) ==
  /\ \E m \in outbox : m[2] = p /\ outbox' = outbox \ {m}
  /\ waited' = [waited EXCEPT ![p][m[1]] = 0]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m[1]}]
  /\ timeout' = [timeout EXCEPT ![p][m[1]] = IF m[1] \in suspect[p] THEN timeout[p][m[1]] + 1 ELSE timeout[p][m[1]]]
  /\ UNCHANGED <<clock, outbox>>

\* The clock wraps back to zero once it exceeds all relevant thresholds,
\* which keeps the state space finite.
ResetClock(p) ==
  /\ clock[p] > SendPoint /\ clock[p] > PredictPoint
  /\ \A q \in Except(Proc, p) : clock[p] > timeout[p][q]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspect, timeout, waited, outbox>>

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p) \/ ResetClock(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A p \in Proc : waited[p] \in [Proc -> Nat]
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ outbox \subseteq Messages

====