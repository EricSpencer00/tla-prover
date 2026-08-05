---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, sending

vars == <<suspicion, timeout, lastHeard, clock, sending>>

\* Correct processes in an eventually perfect failure detector.  Each process
\* periodically sends alive messages (at multiples of SendPoint) and periodically
\* evaluates its suspicion list (at multiples of PredictPoint).  Send and predict
\* clocks never coincide.  timeout is adaptive: it grows when a process that was
\* suspected sends a message that is actually received.
NoMsg == "none"

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ sending = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ sending' = [sending EXCEPT ![p] =
        {m \in Messages : m.dest \in Proc \ {p}}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF timeout[p][q] > lastHeard[p][q] THEN @ + 1 ELSE @]]
  /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] = {q \in suspicion[p] : @} \cup
        {q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q]}]
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF timeout[p][q] > lastHeard[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<timeout, sending>>

Receive(p) ==
  /\ \/ \E q \in Proc :
        /\ q # p
        /\ sending[q] # {}
        /\ \E m \in sending[q] : m.dest = p
        /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = @ \ {q}]
        /\ timeout' = [timeout EXCEPT ![p][q] = IF @ < lastHeard[p][q] THEN @ + 1 ELSE @]
  /\ /\ (\A q \in Proc : q # p => sending[q] = {})
     /\ UNCHANGED <<suspicion, timeout, lastHeard>>
  /\ lastHeard' = [lastHeard EXCEPT ![p] =
        [q \in Proc |-> IF timeout[p][q] > lastHeard[p][q] THEN @ + 1 ELSE @]]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]

WrapClock(p) ==
  /\ clock[p] >= SendPoint
  /\ clock[p] >= PredictPoint
  /\ (\A q \in Proc : timeout[p][q] # 0 => clock[p] >= timeout[p][q])
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspicion, timeout, lastHeard, sending>>

Next == \E p \in Proc :
  SendAlive(p) \/ Predict(p) \/ Receive(p) \/ WrapClock(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ suspicion \in [Proc -> SUBSET Proc]

====