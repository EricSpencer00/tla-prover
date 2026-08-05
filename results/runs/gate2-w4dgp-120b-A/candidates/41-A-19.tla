---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* An eventually perfect failure detector (Chandra & Toueg 1996) for a set of
\* processes that periodically send alive messages and periodically predict
\* who has crashed, each process with its own adaptive timeout interval per
\* other process.
VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

\* The send and predict intervals must never coincide.
IntervalConstraint ==
  /\ SendPoint \in Nat /\ SendPoint > 0
  /\ PredictPoint \in Nat /\ PredictPoint > 0
  /\ (~(SendPoint = PredictPoint))
  /\ (~(SendPoint % PredictPoint = 0))
  /\ (~(PredictPoint % SendPoint = 0))

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

\* A process sends an alive message to every other process.
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages :
                      \E q \in Proc \ {p} : m.to = q /\ m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \in suspect[p] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<suspect, timeout>>

\* A process predicts that a process has crashed once its timeout has elapsed.
PredictCrash(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
        suspect[p] \cup {q \in Proc \ {p} : lastHeard[q] > timeout[p]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \in suspect[p] THEN lastHeard[q] ELSE lastHeard[q] + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* A process receives messages and resets suspicion.
Receive(p) ==
  /\ clock[p] % PredictPoint # 0
  /\ clock[p] % SendPoint # 0
  /\ \E m \in outbox[p] :
       /\ \E q \in Proc \ {p} :
            /\ m.to = p /\ m.from = q
            /\ lastHeard' = [lastHeard EXCEPT ![q] = 0]
            /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q}]
            /\ timeout' = [timeout EXCEPT ![p] =
                  IF q \in suspect[p] THEN timeout[p] + 1 ELSE timeout[p]]
       /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m}]
  /\ clock' = [clock EXCEPT ![p] =
        IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint
              /\ clock[p] + 1 > timeout[p] THEN 0 ELSE clock[p] + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ PredictCrash(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====