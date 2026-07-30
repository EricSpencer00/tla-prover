---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

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
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ \A q \in Proc \ {p} : outgoing' = [outgoing EXCEPT ![p] = @ \cup {[from |-> p, to |-> q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = IF lastHeard[p] < timeout[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : q # p /\ lastHeard[p] > timeout[p]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = IF lastHeard[p] < timeout[p] THEN lastHeard[p] + 1 ELSE lastHeard[p]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ clock' = [clock EXCEPT ![p] = IF @ > timeout[p] /\ @ > SendPoint /\ @ > PredictPoint THEN 0 ELSE @ + 1]
  /\ suspect' = [suspect EXCEPT ![p] = IF @ = {} THEN @ ELSE {}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = 0]
  /\ timeout' = [timeout EXCEPT ![p] = IF suspect[p] # {} THEN @ + 1 ELSE @]
  /\ UNCHANGED <<outgoing>>

Next ==
  \E p \in Proc :
    SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====