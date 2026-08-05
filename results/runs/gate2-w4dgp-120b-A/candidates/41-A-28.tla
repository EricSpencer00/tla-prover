---- MODULE EPFailureDetector ----
EXTENDS Naturals

\* Eventual perfection: correct processes may be slow, so suspicion uses a
\* timeout per sender that grows when a slow message finally arrives.
\* The send and predict clocks are deliberately offset and never equal.
CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outMessages

vars == <<suspect, timeout, lastHeard, clock, outMessages>>

MaxT == 3

TypeOK ==
  /\ \A p \in Proc :
       /\ suspect[p] \subseteq Proc
       /\ timeout[p] \in [Proc -> 0..MaxT]
       /\ lastHeard[p] \in [Proc -> 0..MaxT]
       /\ clock[p] \in 0..MaxT
       /\ outMessages[p] \subseteq Messages

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> 1]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outMessages = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outMessages' = [outMessages EXCEPT ![p] = {m \in Messages : m.to = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] ELSE @]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in suspect[p] THEN lastHeard[p][q] ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, outMessages>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \E m \in outMessages[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![p][m.to] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.to}]
       /\ timeout' = [timeout EXCEPT ![p][m.to] = IF m.to \in suspect[p] THEN @ + 1 ELSE @]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxT THEN 0 ELSE clock[p] + 1]
  /\ outMessages' = [outMessages EXCEPT ![p] = {}]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====