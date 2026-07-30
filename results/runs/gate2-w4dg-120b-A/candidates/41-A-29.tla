---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc
    d0
    SendPoint
    PredictPoint
    Messages

VARIABLES
    suspect
    timeout
    heard
    clock
    outbox

vars == <<suspect, timeout, heard, clock, outbox>>

\* A process p sends an alive message to every other process q.
\* The message is sent out as a pair (p, q) placed in p's outbox.
SendMsg(p) == { m \in Messages : m[1] = p /\ m[2] \in (Proc \ {p}) }

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
    /\ heard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* Alive messages are sent at multiples of SendPoint that are not
\* also multiples of PredictPoint; the two intervals never coincide.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = SendMsg(p)]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ heard' = [heard EXCEPT ![p] = [q \in Proc |-> IF q \in suspect[p] /\ heard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<suspect, timeout>>

\* Predictions happen at multiples of PredictPoint that are not also
\* multiples of SendPoint; one or the other fires, never both.
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] =
                     @ \cup {q \in Proc : q # p /\ heard[p][q] >= timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ heard' = [heard EXCEPT ![p] = [q \in Proc |-> IF heard[p][q] < timeout[p][q] THEN @ + 1 ELSE @]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ ~ (clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~ (clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \E m \in outbox[p] :
         /\ suspect' = [suspect EXCEPT ![p] = @ \ {m[2]}]
         /\ heard' = [heard EXCEPT ![p][m[2]] = 0]
         /\ timeout' = [timeout EXCEPT ![p][m[2]] =
              IF m[2] \in suspect[p] /\ timeout[p][m[2]] < 3 THEN @ + 1 ELSE @]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] =
         IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > 3
         THEN 0 ELSE @ + 1]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ heard \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]

====