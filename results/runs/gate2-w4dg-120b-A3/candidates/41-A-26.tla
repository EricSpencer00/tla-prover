---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES
    suspect, timeout, heard, clock, outbox

vars == <<suspect, timeout, heard, clock, outbox>>

Msg == [to: Proc, from: Proc]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ heard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { [to |-> q, from |-> p] : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ heard' = [heard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN heard[p][q]
                                          ELSE IF heard[p][q] < timeout[p][q] THEN heard[p][q] + 1
                                          ELSE heard[p][q]]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
                      {q \in Proc : q # p /\ heard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ heard' = [heard EXCEPT ![p] = [q \in Proc |-> IF q = p THEN heard[p][q]
                                      ELSE IF heard[p][q] < timeout[p][q] THEN heard[p][q] + 1
                                      ELSE heard[p][q]]]
    /\ UNCHANGED <<timeout, outbox>>

ResetClock(p) ==
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > timeout[p][q]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, heard, outbox>>

Receive(p) ==
    /\ \E m \in Messages, q \in Proc :
        /\ m.from = q
        /\ m.to = p
        /\ heard' = [heard EXCEPT ![p][q] = 0]
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {q}]
        /\ timeout' = [timeout EXCEPT ![p][q] = IF q \in suspect[p] THEN timeout[p][q] + 1 ELSE timeout[p][q]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] < SendPoint THEN clock[p] + 1 ELSE 0]
    /\ UNCHANGED outbox

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : ResetClock(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ heard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

====