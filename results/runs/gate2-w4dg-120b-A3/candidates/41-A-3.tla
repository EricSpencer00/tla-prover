---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

VARIABLES
    suspicion,
    timeout,
    lastHeard,
    clock,
    outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ \A p \in Proc : suspicion[p] \subseteq Proc
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
    /\ \A p \in Proc : clock[p] \in Nat
    /\ \A p \in Proc : outbox[p] \in SUBSET Messages

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] =
                    { m \in Messages : m.sender = p /\ m.dest \in Proc })
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \A q \in Proc :
           /\ lastHeard' = [lastHeard EXCEPT ![p][q] =
                              IF q \in Proc /\ lastHeard[p][q] < timeout[p][q]
                              THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
                        { q \in Proc : lastHeard[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \A q \in Proc :
           lastHeard' = [lastHeard EXCEPT ![p][q] =
                            IF lastHeard[p][q] < timeout[p][q]
                            THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \E M \in SUBSET Messages :
        /\ \A m \in M : m.dest = p
        /\ lastHeard' = [lastHeard EXCEPT ![p] =
                            [q \in Proc |->
                                IF \E m \in M : m.sender = q
                                THEN 0 ELSE @]]
        /\ suspicion' = [suspicion EXCEPT ![p] =
                            suspicion[p] \ { q \in Proc : \E m \in M : m.sender = q }]
        /\ timeout' = [timeout EXCEPT ![p] =
                            [q \in Proc |->
                                IF \E m \in M : m.sender = q /\ q \in suspicion[p]
                                THEN timeout[p][q] + 1
                                ELSE @]]
        /\ outbox' = [outbox EXCEPT ![p] = @ \ M]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec ==
    /\ Init
    /\ [][Next]_vars
    /\ \A p \in Proc :
         UNCHANGED <<clock, outbox, suspicion, timeout, lastHeard>>
         [][\A q \in Proc :
             /\ clock[p] > SendPoint
             /\ clock[p] > PredictPoint
             /\ \A r \in Proc : clock[p] > timeout[p][r]
             /\ clock' = [clock EXCEPT ![p] = 0]
             /\ UNCHANGED <<suspicion, timeout, lastHeard, outbox>>]_vars

====