---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspects, timeout, lastHeard, outbox

vars == <<clock, suspects, timeout, lastHeard, outbox>>

TypeOK ==
    /\ clock \in [Proc -> 0..(SendPoint + PredictPoint + 2)]
    /\ suspects \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspects = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |->
            IF q = p THEN lastHeard[q]
            ELSE [r \in Proc |->
                IF r = p /\ lastHeard[p][r] < timeout[p][r] THEN @ + 1
                ELSE @]]
    /\ UNCHANGED <<suspects, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspects' = [q \in Proc |->
            IF q = p THEN suspects[p]
            ELSE IF lastHeard[p][q] >= timeout[p][q] THEN suspects[p] \cup {q}
            ELSE suspects[p] \ {q}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [q \in Proc |->
            IF q = p THEN lastHeard[p]
            ELSE [r \in Proc |-> IF @[r] < timeout[p][r] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ \E S \in SUBSET {m \in outbox[p] : m.to = p} :
        /\ suspects' = [q \in Proc |->
                IF q = p THEN suspects[p] \ {m.from \in S}
                ELSE suspects[p]]
        /\ timeout' = [q \in Proc |->
                IF q = p THEN [r \in Proc |-> IF r \in {m.from \in S} THEN timeout[p][r] + 1 ELSE timeout[p][r]]
                ELSE timeout[p]]
        /\ lastHeard' = [q \in Proc |->
                IF q = p THEN [r \in Proc |-> IF r \in {m.from \in S} THEN 0 ELSE lastHeard[p][r]]
                ELSE lastHeard[p]]
        /\ outbox' = [outbox EXCEPT ![p] = @ \ S]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]

ResetClocks(p) ==
    /\ clock[p] > 0
    /\ clock[p] >= SendPoint
    /\ clock[p] >= PredictPoint
    /\ \A q \in Proc : clock[p] >= timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspects, timeout, lastHeard, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : ResetClocks(p)

Spec == Init /\ [][Next]_vars

====