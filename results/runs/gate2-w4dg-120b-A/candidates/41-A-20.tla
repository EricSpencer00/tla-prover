---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc,
  d0,
  SendPoint,
  PredictPoint,
  Messages

ASSUME /\ SendPoint \in Nat /\ SendPoint > 0
       /\ PredictPoint \in Nat /\ PredictPoint > 0
       /\ SendPoint # PredictPoint
       /\ \A k \in Nat : SendPoint * k = PredictPoint
       /\ \A k \in Nat : PredictPoint * k = SendPoint

VARIABLES suspect, timeout, lastHeard, clock, outgoing
vars == <<suspect, timeout, lastHeard, clock, outgoing>>

MaxClock == SendPoint + PredictPoint + d0

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ lastHeard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outgoing \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m \in {Messages} /\ m \notin outgoing[p]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                     IF lastHeard[p][q] > timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
                    {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                     IF lastHeard[p][q] > timeout[p][q] THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ \E m \in outgoing[p] :
       /\ lastHeard' = [lastHeard EXCEPT ![p][m] = 0]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m}]
       /\ timeout' = [timeout EXCEPT ![p][m] = IF m \in suspect[p] THEN timeout[p][m] + 1 ELSE timeout[p][m]]
  /\ outgoing' = [outgoing EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] =
                    IF clock[p] >= MaxClock
                    THEN 0
                    ELSE clock[p] + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
  /\ Init /\ [][Next]_vars
  /\ WF_vars(Receive(CHOICE p \in Proc : p))

====