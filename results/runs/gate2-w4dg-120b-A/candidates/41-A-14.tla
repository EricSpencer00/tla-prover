---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME /\ SendPoint \in (Nat \ {0})
       /\ PredictPoint \in (Nat \ {0})
       /\ (SendPoint % PredictPoint # 0) /\ (PredictPoint % SendPoint # 0)

AProc == CHOOSE p \in Proc : TRUE
Preds == { m \in Messages : m.dest = AProc }

VARIABLES suspect, timeout, lastHeard, clock, outbox

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { m \in Preds : m.dest # p }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |-> IF timeout[p][q] < clock[p] + 1
                                      THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q]]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = { q \in Proc : lastHeard[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] >= SendPoint /\ clock[p] >= PredictPoint
                                     /\ \A q \in Proc : clock[p] >= timeout[p][q]
                                     THEN 0 ELSE clock[p] + 1]
    /\ suspect' = [suspect EXCEPT ![p] = { q \in suspect[p] : ~ \E m \in outbox[AProc] : m.dest = q }]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF \E m \in outbox[AProc] : m.dest = q
                                                     THEN 0 ELSE lastHeard[p][q] + 1]]
    /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc |-> IF \E m \in outbox[AProc] : m.dest = q
                                                          THEN @ + 1 ELSE @]]
    /\ UNCHANGED outbox

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====