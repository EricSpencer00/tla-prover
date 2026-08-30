---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspect, timeout, lastHeard, outgoing

vars == <<clock, suspect, timeout, lastHeard, outgoing>>

TypeOK ==
  /\ clock \in 0..(2 * PredictPoint)
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> SUBSET (1..(2 * PredictPoint))]
  /\ lastHeard \in [Proc -> 0..(2 * PredictPoint)]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> {d0}]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.dst = p /\ m.kind = "alive"}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \in suspect[p] /\ lastHeard[p] < 2 * PredictPoint
          THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [p \in Proc |-> suspect[p] \cup
        {q \in Proc : q # p /\ lastHeard[p] > CHOOSE d \in timeout[p] : TRUE}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF lastHeard[p] < 2 * PredictPoint
          THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ (clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0)
  /\ clock[p] # 0
  /\ \E msg \in outgoing[p] :
        /\ msg.dst = p
        /\ lastHeard' = [lastHeard EXCEPT ![msg.src] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {msg.src}]
        /\ timeout' = [q \in Proc |->
              IF q = msg.src /\ q \in suspect[p]
                THEN timeout[p] \cup {CHOOSE d \in timeout[p] : TRUE + 1}
                ELSE timeout[p]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > 2 * PredictPoint THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED <<outgoing>>

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Spec == Init /\ [][Next]_vars

====