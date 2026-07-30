---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
  Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint > 0
       /\ PredictPoint > 0
       /\ SendPoint # PredictPoint
       /\ \A n \in Nat : d0 + n \in Nat

VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

RECURSIVE MaxPlus(_, _)
MaxPlus(f, S) ==
  IF S = {} THEN 0
  ELSE LET x == CHOOSE y \in S : TRUE
       IN f[x] + MaxPlus(f, S \ {x})

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
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.dest = p}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q # p /\ lastHeard[q] < timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[q] > timeout[q]}]
  /\ clock' = [clock EXCEPT ![p] = @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q # p /\ lastHeard[q] <= timeout[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
  /\ outgoing[p] = {}
  /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > MaxPlus(timeout, Proc)
                                    THEN 0 ELSE @ + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q \in suspect[p] /\ q # p THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ suspect' = [p \in Proc |->
        IF p = q /\ q \in suspect[p] THEN suspect[p] \ {q} ELSE suspect[p]]
  /\ timeout' = [p \in Proc |->
        IF p \in suspect[p] THEN timeout[p] + 1 ELSE timeout[p]]
  /\ UNCHANGED outgoing

Next ==
  \/ \E p \in Proc : SendAlive(p)
  \/ \E p \in Proc : Predict(p)
  \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====