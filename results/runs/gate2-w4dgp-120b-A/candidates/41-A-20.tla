---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, interval, lastHeard, clock, toSend

vars == <<suspect, interval, lastHeard, clock, toSend>>

\* Adaptive timeouts: a process suspects another only after not hearing from it
\* for longer than a timeout interval that can grow (it never shrinks) as churn
\* happens.  The clock drives two periodic duties (sending alives, predicting
\* suspicions) that the controller must keep out of phase.

TypeOK ==
  /\ suspect \subseteq [from : Proc, to : Proc]
  /\ interval \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ toSend \subseteq Messages

Init ==
  /\ suspect = {}
  /\ interval = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ toSend = {}

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ toSend' = {m \in Messages : m.from = p /\ m.to # p}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q # p /\ lastHeard[q] < interval[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, interval>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = suspect \cup
        {[from |-> q, to |-> p] : q \in Proc /\ q # p /\ lastHeard[q] > interval[p]}
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q # p /\ lastHeard[q] < interval[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<interval, toSend>>

Threshold(p) == IF interval[p] >= SendPoint THEN interval[p]
                  ELSE IF interval[p] >= PredictPoint THEN interval[p]
                  else IF interval[p] >= 1 THEN interval[p] else 1

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in Messages :
       /\ m.to = p
       /\ suspect' = suspect \ {[from |-> m.from, to |-> p] : m.from # p}
       /\ lastHeard' = [lastHeard EXCEPT ![m.from] = 0]
       /\ interval' = [interval EXCEPT ![m.from] =
                        IF [from |-> m.from, to |-> p] \in suspect
                        THEN interval[m.from] + 1 ELSE interval[m.from]]
       /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > Threshold(p) THEN 0 ELSE @ + 1]
  /\ UNCHANGED toSend

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====