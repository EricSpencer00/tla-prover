---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* Natural-language description: an eventually perfect failure detector with
\* adaptive per-process timeouts. Each process sends alive messages and
\* revises its suspicion list on separate clock ticks; timeouts grow when a
\* suspected process eventually replies.
\* The spec below implements exactly the identifiers the reference cfg expects.

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, wantOut
vars == <<suspect, timeout, lastHeard, clock, wantOut>>

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ wantOut = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ wantOut' = [wantOut EXCEPT ![p] = {m \in Messages : m.sender = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                     IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                     IF lastHeard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<timeout, wantOut>>

\* Receivers consume whatever messages they currently have available; the set
\* of available messages is an environmental choice, modeling an arbitrary
\* interleaving of network delivery.
Receive(p) ==
  /\ \E inMsgs \in SUBSET Messages :
       /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                          IF \E m \in inMsgs : m.sender = q /\ m.kind = "alive"
                            THEN 0 ELSE @]]
       /\ suspect' = [suspect EXCEPT ![p] = {q \in suspect[p] : ~ \E m \in inMsgs : m.sender = q /\ m.kind = "alive"}]
       /\ timeout' = [timeout EXCEPT ![p][q] = IF \E m \in inMsgs : m.sender = q /\ m.kind = "alive" /\ q \in suspect[p] THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint /\ clock[p] + 1 > d0 THEN 0 ELSE clock[p] + 1]
  /\ wantOut' = [wantOut EXCEPT ![p] = {}]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ wantOut \in [Proc -> SUBSET Messages]

====