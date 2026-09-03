---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

Unheard(p, q) == p # q /\ lastHeard[p][q] > timeout[p][q]

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> 0..(d0 + 3)]]
  /\ timeout \in [Proc -> [Proc -> 0..(d0 + 3)]]
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ outgoing \in [Proc -> SUBSET Messages]
  /\ clock \in [Proc -> 0..(d0 + 3)]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] =
        {m \in Messages : m.from = p /\ m.kind = "alive"}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF p # q /\ lastHeard[p][q] <= timeout[p][q]
          THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [p \in Proc |->
        IF Unheard(p, q) THEN suspect[p] \cup {q} ELSE suspect[p]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF lastHeard[p][q] <= timeout[p][q]
          THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ clock[p] <= d0
  /\ \E m \in outgoing[p] :
       /\ m.kind = "alive"
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
       /\ timeout' = [timeout EXCEPT
            ![p] = [q \in Proc |->
                IF q = m.from /\ q \in suspect[p] THEN timeout[p][q] + 1
                ELSE timeout[p][q]]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] = d0 THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED outgoing

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====