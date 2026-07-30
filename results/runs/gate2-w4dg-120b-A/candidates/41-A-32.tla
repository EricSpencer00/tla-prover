---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.who = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q \in suspect[p] /\ clock[p] < timeout[p][q]
                          THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
                    {q \in Proc : (q # p) /\ (lastHeard[p][q] > timeout[p][q])}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q \in suspect[p] /\ clock[p] < timeout[p][q]
                          THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ UNCHANGED <<clock, outbox>>
  /\ \E msg \in outbox[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![p] = [lastHeard[p] EXCEPT ![msg.who] = 0]]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {msg.who}]
       /\ timeout' = [timeout EXCEPT ![p][msg.who] =
                        IF msg.who \in suspect[p] THEN timeout[p][msg.who] + 1
                        ELSE timeout[p][msg.who]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]

ResetClock(p) ==
  /\ clock[p] > SendPoint
  /\ clock[p] > PredictPoint
  /\ \A q \in Proc : clock[p] > timeout[p][q]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)
  \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET Messages]

====