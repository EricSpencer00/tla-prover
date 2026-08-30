---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Indexes and sets, derived from the process set.
Source == Proc
Dest == Proc
Others == Proc \ {d0}

VARIABLES suspect, timeout, clock, lastHeard, outgoing

vars == <<suspect, timeout, clock, lastHeard, outgoing>>
\* The system tracks, per process, which others it suspects (suspect),
\* adaptive timeout intervals (timeout), how long since it last heard
\* from each other (lastHeard), a local clock (clock), and messages it
\* intends to send this transition (outgoing).

TypeOK ==
  /\ lastHeard \in [Source -> [Dest -> Nat]]
  /\ timeout \in [Source -> [Dest -> Nat]]
  /\ suspect \in [Source -> SUBSET Dest]
  /\ outgoing \in [Source -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Source |-> {}]
  /\ timeout = [p \in Source |-> [q \in Dest |-> 1]]
  /\ lastHeard = [p \in Source |-> [q \in Dest |-> 0]]
  /\ clock = [p \in Source |-> 0]
  /\ outgoing = [p \in Source |-> {}]

\* Sending an alive message is gated on the local clock being at a
\* send interval that is not also a predict interval.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT
        ![p] = [q \in Dest |-> IF q \in Others /\ clock[p] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

\* A process predicts based on having timed out on another.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup
        {q \in Others : lastHeard[p][q] >= timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT
        ![p] = [q \in Dest |-> IF q \in Others /\ clock[p] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outgoing>>

\* Receiving any message resets the counter and clears suspicion; an
\* alive message from a suspected process expands that process's timeout.
Receive(p) ==
  /\ \E M \in outgoing[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![p][M.to] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = @ \ {M.to}]
       /\ timeout' = [timeout EXCEPT ![p][M.to] = IF M.to \in suspect[p] THEN @ + 1 ELSE @]
  /\ outgoing' = [outgoing EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint * PredictPoint * 2
                        THEN 1 ELSE @ + 1]

Next == \E p \in Source : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

\* Liveness is not part of the required output for this module.
====