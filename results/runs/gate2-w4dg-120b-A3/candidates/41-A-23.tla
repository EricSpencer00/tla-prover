---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,
  d0,
  SendPoint,
  PredictPoint,
  Messages

\* Behaviors of the correct processes in an eventually perfect failure detector
\* (Chandra & Toueg 1996).  Each process periodically sends alive messages and
\* periodically evaluates who it suspects has crashed, based on an adaptive
\* timeout interval and a last-heard counter.

VARIABLES
  suspect,      \* [Proc -> SUBSET Proc] processes each process currently suspects
  timeOut,      \* [Proc -> [Proc -> Nat]] adaptive timeout interval per peer
  lastHeard,    \* [Proc -> [Proc -> Nat]] time since last heard from each peer
  myClock,      \* [Proc -> Nat] local clock per process
  msgsOut       \* [Proc -> SUBSET Messages] outgoing messages each process wants to send

vars == <<suspect, timeOut, lastHeard, myClock, msgsOut>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeOut \in [Proc -> [Proc -> Nat]]
  /\ \A p \in Proc : timeOut[p][p] = 0
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ \A p \in Proc : lastHeard[p][p] = 0
  /\ myClock \in [Proc -> Nat]
  /\ msgsOut \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeOut = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ myClock = [p \in Proc |-> 0]
  /\ msgsOut = [p \in Proc |-> {}]

\* Send alive messages at a clock multiple of SendPoint (but not PredictPoint).
SendAlive(p) ==
  /\ myClock[p] % SendPoint = 0
  /\ myClock[p] % PredictPoint # 0
  /\ \A q \in Proc \ {p} : msgsOut' = [msgsOut EXCEPT ![p] = msgsOut[p] \cup {<<q>>}]
  /\ myClock' = [myClock EXCEPT ![p] = myClock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeOut>>

\* Predict that peers who have not been heard from past their timeout have crashed.
Predict(p) ==
  /\ myClock[p] % PredictPoint = 0
  /\ myClock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : lastHeard[p][q] > timeOut[p][q]}]
  /\ myClock' = [myClock EXCEPT ![p] = myClock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeOut, msgsOut>>

\* Receive incoming messages, resetting counters and adapting timeouts for suspected peers.
Receive(p) ==
  /\ \A q \in Proc \ {p} : IF <<p>> \in msgsOut[q] THEN TRUE ELSE FALSE
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF <<p>> \in msgsOut[q] THEN 0 ELSE lastHeard[p][q]]]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q \in Proc : <<p>> \in msgsOut[q]}]
  /\ timeOut' = [timeOut EXCEPT ![p] = [q \in Proc |-> IF <<p>> \in msgsOut[q] /\ q \in suspect[p] THEN timeOut[p][q] + 1 ELSE timeOut[p][q]]]
  /\ myClock' = [myClock EXCEPT ![p] = IF myClock[p] >= SendPoint /\ myClock[p] >= PredictPoint /\ myClock[p] >= timeOut[p][p] THEN 0 ELSE myClock[p] + 1]
  /\ msgsOut' = [msgsOut EXCEPT ![p] = {}]

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Spec == Init /\ [][Next]_vars

====