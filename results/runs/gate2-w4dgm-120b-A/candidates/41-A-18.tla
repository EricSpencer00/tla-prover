---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint > 0 /\ PredictPoint > 0 /\ SendPoint # PredictPoint

VARIABLES suspect, timeout, lastHeard, clock, outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

None == "none"

TypeOK ==
  /\ suspect \in [Proc -> SUBSET Proc]
  /\ timeout \in [Proc -> Nat]
  /\ lastHeard \in [Proc -> Nat]
  /\ clock \in [Proc -> Nat]
  /\ outgoing \in [Proc -> SUBSET Messages]

MaxTimeout == IF d0 = 0 THEN 1 ELSE d0 * 2

Init ==
  /\ suspect = [p \in Proc |-> {}]
  /\ timeout = [p \in Proc |-> d0]
  /\ lastHeard = [p \in Proc |-> 0]
  /\ clock = [p \in Proc |-> 0]
  /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
  /\ clock[p] % SendPoint = 0
  /\ clock[p] % PredictPoint # 0
  /\ outgoing' = [outgoing EXCEPT ![p] = {m \in Messages : m.dest \in Proc /\ m.dest # p}]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ lastHeard' = [q \in Proc |->
        IF q # p /\ lastHeard[q] < timeout[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
  /\ clock[p] % PredictPoint = 0
  /\ clock[p] % SendPoint # 0
  /\ suspect' = [q \in Proc |-> IF q = p THEN suspect[p]
                                   ELSE IF q \in suspect[p] \/ lastHeard[q] > timeout[q]
                                           THEN suspect[p] \cup {q} ELSE suspect[p]]
  /\ lastHeard' = [q \in Proc |->
        IF q # p /\ lastHeard[q] < timeout[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<timeout, outgoing>>

Receive(p, m) ==
  /\ m \in outgoing[p]
  /\ outgoing' = [outgoing EXCEPT ![p] = outgoing[p] \ {m}]
  /\ suspect' = [q \in Proc |->
        IF q = p THEN suspect[p] \ {m.dest} ELSE suspect[p]]
  /\ lastHeard' = [q \in Proc |->
        IF q = p /\ m.dest = q THEN 0
        ELSE IF q = p /\ m.dest \in suspect[p] AND timeout[q] < MaxTimeout
               THEN timeout[q] + 1
        ELSE IF q = p THEN timeout[q] ELSE lastHeard[q]]
  /\ UNCHANGED <<timeout, clock>>

Tick(p) ==
  /\ clock[p] % SendPoint # 0
  /\ clock[p] % PredictPoint # 0
  /\ \A m \in outgoing[p] : FALSE
  /\ lastHeard' = [q \in Proc |->
        IF q # p /\ lastHeard[q] < timeout[q] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
  /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
  /\ UNCHANGED <<suspect, timeout, outgoing>>

ResetClock(p) ==
  /\ clock[p] > SendPoint + PredictPoint + MaxTimeout
  /\ clock' = [clock EXCEPT ![p] = 0]
  /\ UNCHANGED <<suspect, timeout, lastHeard, outgoing>>

Next ==
  \/ \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Tick(p) \/ ResetClock(p)
  \/ \E p \in Proc, m \in Messages : Receive(p, m)

Spec == Init /\ [][Next]_vars

====