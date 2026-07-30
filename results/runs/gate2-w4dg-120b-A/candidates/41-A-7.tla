---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

ASSUME SendPoint \in Nat /\ PredictPoint \in Nat /\ SendPoint > 0 /\ PredictPoint > 0
ASSUME SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0

VARIABLES suspectFrom, timeoutFor, lastFrom, clock, pending

MessageFrom(msg) == msg
MessageTo(msg) == msg

TypeOK ==
    /\ suspectFrom \in [Proc -> SUBSET Proc]
    /\ timeoutFor \in [Proc -> [Proc -> Nat]]
    /\ lastFrom \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ pending \in [Proc -> SUBSET Messages]

Init ==
    /\ suspectFrom = [p \in Proc |-> {}]
    /\ timeoutFor = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastFrom = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ pending = [p \in Proc |-> {}]

\* A process sends alive messages to all others, but never at the same
\* clock value another process makes predictions, because SendPoint and
\* PredictPoint are never multiples of each other.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ pending' = [pending EXCEPT ![p] = Messages]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastFrom' = [lastFrom EXCEPT ![p] =
                        [q \in Proc |->
                            IF q = p
                                THEN 0
                                ELSE IF lastFrom[p][q] < timeoutFor[p][q]
                                    THEN lastFrom[p][q] + 1
                                    ELSE lastFrom[p][q]]]
    /\ UNCHANGED <<suspectFrom, timeoutFor>>

MakePrediction(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspectFrom' = [suspectFrom EXCEPT ![p] =
                         @ \cup {q \in Proc : lastFrom[p][q] > timeoutFor[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastFrom' = [lastFrom EXCEPT ![p] =
                        [q \in Proc |->
                            IF lastFrom[p][q] < timeoutFor[p][q]
                                THEN lastFrom[p][q] + 1
                                ELSE lastFrom[p][q]]]
    /\ UNCHANGED <<timeoutFor, pending>>

Receive(p) ==
    /\ pending' = [pending EXCEPT ![p] = {}]
    /\ suspectFrom' = [suspectFrom EXCEPT ![p] =
                         @ \ {q \in Proc : q \in pending[p] /\ @}]
    /\ lastFrom' = [lastFrom EXCEPT ![p] = [q \in Proc |->
                         IF q \in pending[p] THEN 0 ELSE @]]
    /\ timeoutFor' = [timeoutFor EXCEPT ![p] = [q \in Proc |->
                         IF q \in pending[p] /\ q \in suspectFrom[p]
                            THEN @ + 1
                            ELSE @]]
    /\ clock' = [clock EXCEPT ![p] =
                    IF clock[p] + 1 > SendPoint /\ clock[p] + 1 > PredictPoint
                           /\ \A q \in Proc : clock[p] + 1 > timeoutFor[p][q]
                        THEN 0
                        ELSE clock[p] + 1]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : MakePrediction(p)
    \/ \E p \in Proc : Receive(p)

vars == <<suspectFrom, timeoutFor, lastFrom, clock, pending>>
Spec == Init /\ [][Next]_vars

====