---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeoutFor, lastHeard, clock, pending

vars == <<suspect, timeoutFor, lastHeard, clock, pending>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeoutFor \in [Proc -> [Proc -> Nat]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ clock \in [Proc -> Nat]
    /\ pending \in [Proc -> SUBSET Messages]

SomeProcess == CHOOSE p \in Proc : TRUE

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeoutFor = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ pending = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = [pending EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF timeoutFor[p][q] = 0 THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspect, timeoutFor>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : q # p /\ lastHeard[p][q] > timeoutFor[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF timeoutFor[p][q] = 0 THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeoutFor, pending>>

Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ pending' = [pending EXCEPT ![p] = {}]
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from : m \in pending[p]}]
    /\ timeoutFor' = [timeoutFor EXCEPT ![p] = [q \in Proc |->
                            IF q \in {m.from : m \in pending[p]} /\ q \in suspect[p]
                            THEN timeoutFor[p][q] + 1 ELSE timeoutFor[p][q]]]
    /\ clock' = IF clock[p] > SendPoint /\ clock[p] > PredictPoint /\ \A q \in Proc : clock[p] > timeoutFor[p][q]
                 THEN 0 ELSE clock[p] + 1
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF q \in {m.from : m \in pending[p]} THEN 0 ELSE IF timeoutFor[p][q] = 0 THEN lastHeard[p][q] ELSE lastHeard[p][q] + 1]]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(\E p \in Proc : SendAlive(p))
    /\ WF_vars(\E p \in Proc : Predict(p))
    /\ WF_vars(\E p \in Proc : Receive(p))

====