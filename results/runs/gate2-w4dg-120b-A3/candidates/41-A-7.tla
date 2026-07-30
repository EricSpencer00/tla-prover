---- MODULE EPFailureDetector ----
EXTENDS Integers

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES
    suspect, timeout, heard, clock, outbox

vars == <<suspect, timeout, heard, clock, outbox>>

Neighbors(p) == Proc \ {p}

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Neighbors(p) |-> d0]]
    /\ heard = [p \in Proc |-> [q \in Neighbors(p) |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {msg \in Messages : msg.to \in Neighbors(p)}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ heard' = [heard EXCEPT ![p] = [q \in Neighbors(p) |-> IF clock[p] > timeout[p][q] THEN heard[p][q] ELSE heard[p][q] + 1]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in Neighbors(p) : heard[p][q] > timeout[p][q]}]
    /\ heard' = [heard EXCEPT ![p] = [q \in Neighbors(p) |-> IF clock[p] > timeout[p][q] THEN heard[p][q] ELSE heard[p][q] + 1]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ ({q \in Neighbors(p) : \E m \in outbox[q] : m.to = p}] \cup {q \in Neighbors(p) : \E m \in outbox[q] : m.to = p})]
    /\ timeout' = [timeout EXCEPT ![p][q] =
                        IF suspect[p] \cup {q} \subseteq suspect[q] \cup {p} THEN timeout[p][q] + 1 ELSE timeout[p][q]]
    /\ heard' = [heard EXCEPT ![p] = [q \in Neighbors(p) |-> IF \E m \in outbox[q] : m.to = p THEN 0 ELSE IF clock[p] > timeout[p][q] THEN heard[p][q] ELSE heard[p][q] + 1]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] < SendPoint /\ clock[p] < PredictPoint /\ \A q \in Neighbors(p) : clock[p] < timeout[p][q] THEN clock[p] + 1 ELSE 0]
    /\ outbox' = [outbox EXCEPT ![p] = {}]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
    /\ Init
    /\ [][Next]_vars

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> INTEGER]]
    /\ heard \in [Proc -> [Proc -> INTEGER]]
    /\ clock \in [Proc -> INTEGER]
    /\ outbox \in [Proc -> SUBSET Messages]

====