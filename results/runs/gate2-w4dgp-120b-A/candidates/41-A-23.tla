---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint # PredictPoint
       /\ SendPoint # 0
       /\ PredictPoint # 0
       /\ d0 # 0

VARIABLES sus, d, lastH, clockv, want
vars == <<sus, d, lastH, clockv, want>>

TypeOK ==
  /\ sus \in [Proc -> SUBSET Proc]
  /\ d \in [Proc -> Nat]
  /\ lastH \in [Proc -> Nat]
  /\ clockv \in [Proc -> Nat]
  /\ want \in [Proc -> SUBSET Messages]

Init ==
  /\ sus = [p \in Proc |-> {}]
  /\ d = [p \in Proc |-> d0]
  /\ lastH = [p \in Proc |-> 0]
  /\ clockv = [p \in Proc |-> 0]
  /\ want = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clockv[p] % SendPoint = 0
  /\ clockv[p] % PredictPoint # 0
  /\ want' = [want EXCEPT ![p] = {q \in Proc : q # p}]
  /\ clockv' = [clockv EXCEPT ![p] = @ + 1]
  /\ lastH' = [q \in Proc |->
        IF lastH[q] < d[p] AND q # p THEN lastH[q] + 1 ELSE lastH[q]]
  /\ UNCHANGED <<sus, d>>

Predict(p) ==
  /\ clockv[p] % PredictPoint = 0
  /\ clockv[p] % SendPoint # 0
  /\ sus' = [sus EXCEPT ![p] = @ \cup {q \in Proc : lastH[q] > d[p]}]
  /\ lastH' = [q \in Proc |->
        IF lastH[q] < d[p] AND q # p THEN lastH[q] + 1 ELSE lastH[q]]
  /\ clockv' = [clockv EXCEPT ![p] = @ + 1]
  /\ UNCHANGED <<d, want>>

Receive(p) ==
  /\ clockv[p] % SendPoint # 0
  /\ clockv[p] % PredictPoint # 0
  /\ sus' = [sus EXCEPT ![p] = @ \cup (want[p] \cap {q \in Proc : q # p})]
  /\ d' = [q \in Proc |-> IF q \in sus[p] THEN d[p] + 1 ELSE d[p]]
  /\ lastH' = [q \in Proc |->
        IF q \in want[p] AND q # p THEN 0
        ELSE IF lastH[q] < d[p] AND q # p THEN lastH[q] + 1
        ELSE lastH[q]]
  /\ clockv' = [clockv EXCEPT ![p] = IF @ < d[p] THEN @ + 1 ELSE 0]
  /\ want' = [want EXCEPT ![p] = {}]

Next ==
  \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====