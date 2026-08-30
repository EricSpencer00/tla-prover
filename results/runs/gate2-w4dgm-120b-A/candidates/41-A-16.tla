---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages
ASSUME d0 \notin Proc /\ SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint # PredictPoint

VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> 1]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.from = p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \notin suspect[p] /\ q # p THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
        {q \in Proc : lastHeard[q] > timeout[p] /\ q # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \notin suspect[p] /\ q # p THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ clock[p] % SendPoint != 0
  /\ clock[p] % PredictPoint != 0
  /\ clock[p] > 0
  /\ lastHeard' = [lastHeard EXCEPT ![p] = 0]
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {p}]
  /\ timeout' = [timeout EXCEPT ![p] = IF p \in suspect[p] THEN @ + 1 ELSE @]
  /\ outgoing' = [outgoing EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] =
        IF clock[p] >= (SendPoint * PredictPoint * timeout[p]) THEN 0 ELSE clock[p] + 1]

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====