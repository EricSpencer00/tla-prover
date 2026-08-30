---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspect, timeout, lastHeard, localClock, outbox

vars == <<suspect, timeout, lastHeard, localClock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Int]]
    /\ localClock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ localClock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ localClock[p] % SendPoint = 0
    /\ localClock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ localClock' = [localClock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF timeout[p][q] > lastHeard[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ localClock[p] % PredictPoint = 0
    /\ localClock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ localClock' = [localClock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF timeout[p][q] > lastHeard[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ localClock[p] % SendPoint # 0
    /\ localClock[p] % PredictPoint # 0
    /\ \E m \in outbox[p] :
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![p][m.from] = IF m.from \in suspect[p] THEN @ + 1 ELSE @]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ localClock' = [localClock EXCEPT ![p] =
                        IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint
                            /\ \A q \in Proc : @ + 1 > timeout[p][q]
                        THEN 0 ELSE @ + 1]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====