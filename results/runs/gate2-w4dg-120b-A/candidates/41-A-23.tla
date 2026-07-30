---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

VARIABLES
    suspect,
    timeout,
    lastHeard,
    clock,
    outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

MsgDomain == {m \in Messages : m.from \in Proc /\ m.to \in Proc /\ m.from # m.to}

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outgoing \in [Proc -> SUBSET MsgDomain]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = {m \in MsgDomain : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN 0 ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup {q \in Proc : lastHeard[p][q] >= timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN 0 ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ LET recv == {m \in Messages : m.to = p /\ m.from \in Proc} IN
         /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q \in {m.from : m \in recv} THEN 0 ELSE IF lastHeard[p][q] > 0 THEN lastHeard[p][q] - 1 ELSE 0]]
         /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q \in Proc : q \in {m.from : m \in recv}}]
         /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |-> IF q \in {m.from : m \in recv} /\ q \in suspect[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] > SendPoint /\ clock[p] > PredictPoint /\ \A q \in Proc : clock[p] > timeout[p][q] THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED outgoing

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====