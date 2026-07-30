---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES
  suspect, timeout, heard, clock, outbox

MsgParts == [from : Proc, to : Proc]

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> [Proc -> Nat]]
  /\ heard \in [Proc -> [Proc -> Nat]]
  /\ clock \in [Proc -> Nat]
  /\ outbox \in [Proc -> SUBSET MsgParts]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
  /\ heard = [p \in Proc |-> [q \in Proc |-> 0]]
  /\ clock = [p \in Proc |-> 0]
  /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outbox[p] = {}
  /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.to = p /\ m.from # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ heard' = [heard EXCEPT ![p] = [q \in Proc |->
        IF timeout[p][q] = 0 THEN heard[p][q] ELSE heard[p][q] + 1]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] =
        {q \in Proc : heard[p][q] >= timeout[p][q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ heard' = [heard EXCEPT ![p] = [q \in Proc |->
        IF timeout[p][q] = 0 THEN heard[p][q] ELSE heard[p][q] + 1]]
  /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
  /\ ~ (clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
  /\ ~ (clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
  /\ LET base ==
        {q \in Proc :
           \E m \in outbox[q] : m.to = p /\ m.from = q}
     IN
     /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ base]
     /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |->
          IF q \in base /\ suspect[p][q] THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
  /\ heard' = [heard EXCEPT ![p] = [q \in Proc |->
        IF q \in base THEN 0 ELSE heard[p][q]]]
  /\ outbox' = [outbox EXCEPT ![p] = {}]
  /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= SendPoint
                                      /\ clock[p] >= PredictPoint
                                      /\ \A q \in Proc : clock[p] >= timeout[p][q]
                                      THEN 0 ELSE clock[p] + 1]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_<<suspect, timeout, heard, clock, outbox>>

====