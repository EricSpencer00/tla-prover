---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outgoing

vars == <<suspicion, timeout, lastHeard, clock, outgoing>>

TypeOK ==
  /\ suspicion \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ suspicion = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.dst = q}]

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspicion' = [suspicion EXCEPT ![p] =
        @ \cup {q \in Proc : lastHeard[p] > timeout[p]}]

Receive(p) ==
  /\ \E m \in outgoing[p] :
        /\ lastHeard' = [lastHeard EXCEPT ![m.dst] = 0]
        /\ suspicion' = [suspicion EXCEPT ![m.dst] = @ \ {p}]
        /\ timeout' = [timeout EXCEPT ![m.dst] =
             IF m.dst \in suspicion[p] THEN @ + 1 ELSE @]
  /\ outgoing' = [outgoing EXCEPT ![p] = {}]

TimerTick(p) ==
  /\ clock[p] = 0 \/ clock[p] >= SendPoint
  /\ clock[p] >= PredictPoint
  /\ \A q \in Proc : clock[p] >= timeout[p]
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = IF lastHeard[p] < timeout[p] THEN lastHeard[p] + 1 ELSE timeout[p]]
  /\ UNCHANGED <<suspicion, timeout, outgoing>>

Next ==
  \E p \in Proc :
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ TimerTick(p)

Spec == Init /\ [][Next]_vars

====