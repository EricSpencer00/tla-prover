---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbound

vars == <<suspect, timeout, lastHeard, clock, outbound>>

Last(p, q) == lastHeard[p][q]
Incr(p, q) == IF Last(p, q) < timeout[p][q] THEN Last(p, q) + 1 ELSE timeout[p][q]

TypeOK ==
    /\ \A p \in Proc : suspect[p] \subseteq Proc
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
    /\ \A p \in Proc : clock[p] \in Nat
    /\ \A p \in Proc : outbound[p] \subseteq Messages

Init ==
    /\ \A p \in Proc : suspect[p] = {}
    /\ \A p \in Proc : timeout[p] = [q \in Proc |-> d0]
    /\ \A p \in Proc : lastHeard[p] = [q \in Proc |-> 0]
    /\ \A p \in Proc : clock[p] = 0
    /\ \A p \in Proc : outbound[p] = {}

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbound' = [outbound EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0 ELSE Incr(p, q)]]

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : clock[p] > timeout[p][q] /\ q \notin @}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN 0 ELSE Incr(p, q)]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E r \in Proc :
         /\ r # p
         /\ Cardinality(outbound[r] \cap {m \in Messages : m.to = p}) > 0
         /\ lastHeard' = [lastHeard EXCEPT ![p][r] = 0]
         /\ suspect' = [suspect EXCEPT ![p] = @ \ {r}]
         /\ timeout' = [timeout EXCEPT ![p][r] = IF r \in suspect[p] THEN @ + 1 ELSE @]
    /\ outbound' = [outbound EXCEPT ![r] = {m \in outbound[r] : m.to # p}]
    /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint * PredictPoint * d0 THEN 0 ELSE @ + 1]

Next == \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====