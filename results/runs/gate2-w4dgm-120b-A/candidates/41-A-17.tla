---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ SendPoint # PredictPoint
       /\ d0 \in Nat /\ d0 > 0

\* send/receive/outbox as a message stamped with its origin; it always arrives
Message == [src : Proc, dest : Proc, stamp : Messages]

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

\* A process sends alive messages to every other process at its send tick
SendAlive(p) ==
  /\ clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] =
                  {[src |-> p, dest |-> q, stamp |-> "alive"] : q \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
                     [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                   THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

\* A process suspects anyone it has not heard from past that process's timeout
Predict(p) ==
  /\ clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
                  @ \cup {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
                     [q \in Proc |-> IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                   THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outbox>>

\* Receiving an alive message resets the heard counter and clears the suspicion
Receive(p) ==
  /\ clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0
  /\ \E m \in outbox[p] :
       /\ m.dest = p
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.src] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.src}]
       /\ timeout' = [timeout EXCEPT ![p][m.src] =
                        IF m.src \in suspect[p] THEN timeout[p][m.src] + 1 ELSE timeout[p][m.src]]
       /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > SendPoint \/ clock[p] + 1 > PredictPoint
                                            \/ clock[p] + 1 > d0 \/ clock[p] + 1 > timeout[p][p]
                                            THEN 0 ELSE clock[p] + 1]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspect \subseteq Proc
  /\ outbox \subseteq Message

====