---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint # 0 /\ PredictPoint # 0 /\ SendPoint # PredictPoint

VARIABLES suspects, timeout, lastHeard, clock, outgoing

vars == <<suspects, timeout, lastHeard, clock, outgoing>>

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> 0 .. 2]]
  /\ timeout \in [Proc -> [Proc -> 1 .. 2]]
  /\ suspects \subseteq [suspicions : Proc]
  /\ outgoing \subseteq Messages
  /\ clock \in [Proc -> 0 .. 2]

Init ==
  /\ suspects = {}
  /\ timeout = [p \in Proc |-> [q \in Proc |-> 1]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = { [from |-> p, to |-> q] : q \in Proc }
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF q \in suspects THEN lastHeard[p][q] + 1
                      ELSE lastHeard[p][q]]]
  /\ UNCHANGED <<suspects, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspects' = suspects \cup
       {[suspicions |-> q] : q \in Proc : lastHeard[p][q] > timeout[p][q]}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> lastHeard[p][q] + 1]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E r \in {x \in Messages : x.to = p} :
       /\ lastHeard' = [lastHeard EXCEPT ![p][r.from] = 0]
       /\ suspects' = suspects \ {[suspicions |-> r.from]}
       /\ timeout' = [timeout EXCEPT ![p][r.from] =
                        IF r.from \in suspects THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > 2 THEN 0 ELSE clock[p] + 1]
  /\ UNCHANGED outgoing

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====