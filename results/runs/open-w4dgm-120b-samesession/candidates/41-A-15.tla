---- MODULE EPFailureDetector ----
EXTENDS Naturals

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

NoMsg == [dest |-> "none", tag |-> "none"]

VARIABLES suspect, timeout, heardAfter, clock, outbox

vars == <<suspect, timeout, heardAfter, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ heardAfter \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ heardAfter = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {NoMsg}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in outbox[p] : m.dest = "none"}
                                             \cup {[dest |-> q, tag |-> "alive"] : q \in Proc \ {p}}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ heardAfter' = [heardAfter EXCEPT ![p] = [q \in Proc |-> IF heardAfter[p][q] < timeout[p][q] THEN heardAfter[p][q] + 1 ELSE timeout[p][q]]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = {q \in Proc \ {p} : heardAfter[p][q] > timeout[p][q]}]
    /\ heardAfter' = [heardAfter EXCEPT ![p] = [q \in Proc |-> IF heardAfter[p][q] < timeout[p][q] THEN heardAfter[p][q] + 1 ELSE timeout[p][q]]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ outbox[p] # {NoMsg}
    /\ suspect' = [q \in Proc |-> IF q = p THEN suspect[p]
                                   ELSE IF \E m \in outbox[p] : m.dest = q /\ m.tag = "alive" THEN suspect[p] \ {q} ELSE suspect[p] ]
    /\ timeout' = [q \in Proc |-> IF q = p THEN timeout[p]
                                   ELSE IF \E m \in outbox[p] : m.dest = q /\ m.tag = "alive" /\ q \in suspect[p] THEN timeout[p][q] + 1
                                          ELSE timeout[p][q] ]
    /\ heardAfter' = [q \in Proc |-> IF \E m \in outbox[p] : m.dest = q /\ m.tag = "alive" THEN 0
                                         ELSE IF heardAfter[p][q] < timeout[p][q] THEN heardAfter[p][q] + 1 ELSE timeout[p][q] ]
    /\ outbox' = [outbox EXCEPT ![p] = {NoMsg}]
    /\ UNCHANGED clock

ResetClock(p) ==
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, heardAfter, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_vars

====