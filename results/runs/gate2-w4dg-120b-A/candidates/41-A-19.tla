---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES
    suspect, timeout, heard, clock, outbox

vars == <<suspect, timeout, heard, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ heard \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [q \in Proc |-> d0]
    /\ heard = [q \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.dst = p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ heard' = [q \in Proc |->
                    IF q = p \/ ((@ - 1) % SendPoint = 0) THEN @ ELSE @ + 1]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : heard[q] >= timeout[q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ heard' = [q \in Proc |->
                    IF q = p \/ ((@ - 1) % PredictPoint = 0) THEN @ ELSE @ + 1]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ suspect' = [suspect EXCEPT ![p] = @ \ {q \in Proc : \E m \in Messages : m.dst = p /\ m.src = q}]
    /\ timeout' = [q \in Proc |->
                    IF \E m \in Messages : m.dst = p /\ m.src = q /\ q \in suspect[p] THEN timeout[q] + 1 ELSE @]
    /\ heard' = [q \in Proc |->
                    IF \E m \in Messages : m.dst = p /\ m.src = q THEN 0 ELSE @]
    /\ clock' = [clock EXCEPT ![p] =
                    IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > d0 + 1
                    THEN 0 ELSE @ + 1]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====