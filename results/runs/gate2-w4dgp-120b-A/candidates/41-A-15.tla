---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, heard, clock, msgset

vars == <<suspect, timeout, heard, clock, msgset>>

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ heard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ msgset \in [Proc -> SUBSET Messages]

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ heard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ msgset = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ msgset' = [msgset EXCEPT ![p] = {m \in Messages : m.receiver # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ heard' = [q \in Proc |->
        IF q # p /\ clock[p] < timeout[q] THEN heard[q] + 1 ELSE heard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : heard[q] > timeout[q]}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ heard' = [q \in Proc |->
        IF clock[p] < timeout[q] THEN heard[q] + 1 ELSE heard[q]]
  /\ UNCHANGED <<timeout, msgset>>

Receive(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ msgset' = [msgset EXCEPT ![p] = {}]
  /\ suspect' = [suspect EXCEPT ![p] = @ \ {q \in Proc : \E m \in msgset[p] : m.receiver = q}]
  /\ heard' = [q \in Proc |-> IF \E m \in msgset[p] : m.receiver = q THEN 0 ELSE heard[q]]
  /\ timeout' = [q \in Proc |->
        IF (q \in suspect[p]) /\ (\E m \in msgset[p] : m.receiver = q) THEN timeout[q] + 1 ELSE timeout[q]]
  /\ clock' = [p \in Proc |-> IF clock[p] > SendPoint /\ clock[p] > PredictPoint /\ \A q \in Proc : clock[p] > timeout[q]
                          THEN 0 ELSE clock[p]]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====