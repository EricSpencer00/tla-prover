---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

\* Each process acts as sender and receiver, maintaining a suspicion set,
\* an adaptive timeout, a last-heard counter, and a local clock.
\* Send and predict operations are timed by the clock and never coincide.

TypeOK ==
  /\ \A p \in Proc : suspicion[p] \subseteq Proc
  /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
  /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
  /\ \A p \in Proc : clock[p] \in Nat
  /\ \A p \in Proc : outbox[p] \subseteq Messages

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p /\ m.to # p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = @ \cup
        {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
        IF lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  LET newHeard == {m.from \in Proc :
                      \E m \in outbox[p] : m.to = p} IN
  LET newS == suspicion[p] \newHeard IN
  LET newT == [q \in Proc |-> IF q \in newS /\ q \in newHeard THEN @ + 1 ELSE @] IN
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ suspicion' = [suspicion EXCEPT ![p] = newS]
  /\ timeout' = [timeout EXCEPT ![p] = newT]
  /\ lastHeard' = IF newHeard = {}
       THEN [lastHeard EXCEPT ![p] = [q \in Proc |->
                  IF lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
       ELSE [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in newHeard THEN 0 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > timeout[p][p]
                     THEN 0 ELSE clock[p] + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====