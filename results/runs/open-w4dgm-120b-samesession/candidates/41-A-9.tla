---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat /\ SendPoint >= 1
       /\ PredictPoint \in Nat /\ PredictPoint >= 1
       /\ SendPoint # PredictPoint

VARIABLES clock, suspects, timeout, lastHeard, outgoing

vars == <<clock, suspects, timeout, lastHeard, outgoing>>

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspects \in [Proc -> SUBSET Proc]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ clock = [p \in Proc |-> 0]
  /\ suspects = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.here = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in suspects[p] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<suspects, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspects' = [suspects EXCEPT ![p] = @ \union
                    {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> @ + 1]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E q \in Proc :
       /\ q # p
       /\ \E m \in outgoing[q] : m.here = q
       /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
       /\ suspects' = [suspects EXCEPT ![p] = @ \ {q}]
       /\ timeout' = [timeout EXCEPT ![p][q] = IF q \in suspects[p] THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint + PredictPoint + d0 + 1
                                   THEN 0 ELSE @ + 1]
  /\ UNCHANGED outgoing

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Receive(CHOOSEN(Proc)))

====