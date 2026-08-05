---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ SendPoint # PredictPoint
       /\ d0 \in Nat /\ d0 > 0

VARIABLES suspect, timeout, lastHeard, clock, pending

vars == <<suspect, timeout, lastHeard, clock, pending>>

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ pending = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ (clock[p] % SendPoint) = 0
  /\ (clock[p] % PredictPoint) # 0
  /\ pending' = [pending EXCEPT ![p] = {m \in Messages : m.to = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                       IF timeout[p][q] < clock[p] THEN @ [q] + 1 ELSE @ [q]]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ (clock[p] % PredictPoint) = 0
  /\ (clock[p] % SendPoint) # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup
                   {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                       IF timeout[p][q] < clock[p] THEN @ [q] + 1 ELSE @ [q]]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, pending>>

Receive(p) ==
  /\ (clock[p] % SendPoint) # 0
  /\ (clock[p] % PredictPoint) # 0
  /\ \E S \in Messages :
       /\ S.to = p
       /\ suspect' = [suspect EXCEPT ![p] = @ \ {S.from}]
       /\ timeout' = [timeout EXCEPT ![p][S.from] =
                       IF S.from \in suspect[p] THEN @ + 1 ELSE @]
       /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                       IF q = S.from THEN 0
                       ELSE IF timeout[p][q] < clock[p] THEN @ [q] + 1 ELSE @ [q]]]
  /\ clock' = [clock EXCEPT ![p] =
                 IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint
                    /\ \A r \in Proc : @ > timeout[p][r]
                 THEN 0 ELSE @ + 1]
  /\ UNCHANGED pending

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ \A p \in Proc : suspect[p] \subseteq Proc
  /\ \A p \in Proc : pending[p] \subseteq Messages

====