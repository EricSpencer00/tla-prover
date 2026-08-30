---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspects, timeout, notHeard, clock, toSend

vars == <<suspects, timeout, notHeard, clock, toSend>>

TypeOK ==
    /\ suspects \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ notHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ toSend \in [Proc -> SUBSET Messages]

Init ==
    /\ suspects = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ notHeard = [p \in Proc |-> [r \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ toSend = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0 \/ clock[p] = 0
    /\ clock[p] % PredictPoint # 0
    /\ toSend' = [toSend EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ notHeard' = [r \in Proc |->
                     IF r = p THEN notHeard[p][r]
                     ELSE IF notHeard[p][r] < timeout[p] THEN notHeard[p][r] + 1
                     ELSE notHeard[p][r]]
    /\ UNCHANGED <<suspects, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0 \/ clock[p] = 0
    /\ clock[p] % SendPoint # 0
    /\ suspects' = [suspects EXCEPT
                      ![p] = suspects[p] \cup
                                {r \in Proc : notHeard[p][r] > timeout[p]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ notHeard' = [r \in Proc |->
                     IF r = p THEN notHeard[p][r]
                     ELSE IF notHeard[p][r] < timeout[p] THEN notHeard[p][r] + 1
                     ELSE notHeard[p][r]]
    /\ UNCHANGED <<timeout, toSend>>

Receive(p, m) ==
    /\ m \in toSend[p]
    /\ toSend' = [toSend EXCEPT ![p] = toSend[p] \ {m}]
    /\ notHeard' = [notHeard EXCEPT ![p][m.from] = 0]
    /\ suspects' = [suspects EXCEPT ![p] = suspects[p] \ {m.from}]
    /\ timeout' = [timeout EXCEPT ![p] =
                     IF m.from \in suspects[p] THEN timeout[p] + 1 ELSE timeout[p]]
    /\ clock' = IF clock[p] > 0 THEN clock[p] - 1 ELSE 0

Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ \E m \in Messages : Receive(p, m)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ WF_vars(SendAlive("p1"))
    /\ SF_vars(Predict("p1"))
    /\ WF_vars(SendAlive("p2"))
    /\ SF_vars(Predict("p2"))
    /\ WF_vars(SendAlive("p3"))
    /\ SF_vars(Predict("p3"))

====