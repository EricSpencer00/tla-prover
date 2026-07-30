---- MODULE EPFailureDetector ----
EXTENDS Integers

\* This module follows the description above: correct processes send alive
\* messages and predict crashes under an eventually perfect failure
\* detector. send and predict actions are clock-driven and never coincide.
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

NoOne == "noone"

VARIABLES suspicion, timeout, lastHeard, clock, outgoing

vars == <<suspicion, timeout, lastHeard, clock, outgoing>>

\* A process q is timed out for p when p has not heard from q within the
\* current adaptive timeout interval that p holds for q.
TimedOut(p, q) ==
  /\ q \notin suspicion[p]
  /\ lastHeard[p][q] > timeout[p][q]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

\* Send alive messages to every other process.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.rcpt # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                      IF q = p THEN 0
                      ELSE IF lastHeard[p][q] < timeout[p][q]
                        THEN lastHeard[p][q] + 1
                        ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspicion, timeout>>

\* Predict crashes for any process that has timed out.
Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = {q \in Proc : TimedOut(p, q)}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                      IF lastHeard[p][q] < timeout[p][q]
                        THEN lastHeard[p][q] + 1
                        ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outgoing>>

\* Receive any incoming messages addressed to p.
Receive(p) ==
  /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ \E S \in SUBSET Messages :
       /\ \A m \in S : m.rcpt = p
       /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {m.sender : m \in S}]
       /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |->
                          IF \E m \in S : m.sender = q /\ m.type = "alive"
                            THEN timeout[p][q] + 1
                          ELSE timeout[p][q]]]
       /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                          IF \E m \in S : m.sender = q THEN 0 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] <= 3
                                     THEN clock[p] + 1
                                     ELSE 0]
  /\ UNCHANGED <<outgoing>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \subseteq [p \in Proc, q \in Proc |-> BOOLEAN]
  /\ outgoing \subseteq [rcpt : Proc, sender : Proc \cup {NoOne}, type : {"alive"}]

====