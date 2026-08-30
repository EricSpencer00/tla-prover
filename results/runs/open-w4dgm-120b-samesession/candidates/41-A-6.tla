---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, clock, outbound
vars == <<suspect, timeout, lastHeard, clock, outbound>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outbound \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outbound = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbound' = [outbound EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \notin suspect[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \union {q \in Proc : q # p /\ lastHeard[q] > timeout[p]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [q \in Proc |-> IF q \notin suspect[p] THEN lastHeard[q] + 1 ELSE lastHeard[q]]
    /\ UNCHANGED <<timeout, outbound>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E q \in Proc :
         \/ \E m \in outbound[q] : m.from = q
         /\ suspect' = [suspect EXCEPT ![p] = @ \ {q}]
         /\ lastHeard' = [lastHeard EXCEPT ![q] = 0]
         /\ timeout' = [timeout EXCEPT ![q] = IF q \in suspect[p] THEN timeout[p] + 1 ELSE timeout[p]]
    /\ clock' = [clock EXCEPT ![p] = IF @ > 1 + SendPoint + PredictPoint + timeout[p] THEN 0 ELSE @ + 1]
    /\ UNCHANGED outbound

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Proc : SendAlive(p))
    /\ WF_vars(\E p \in Proc : Predict(p))
    /\ WF_vars(\E p \in Proc : Receive(p))

SpecOK == Spec /\ TRUE
====