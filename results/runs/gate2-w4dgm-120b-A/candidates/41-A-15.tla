---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

\* Each process sends alive messages on multiples of SendPoint and predicts
\* crashes on multiples of PredictPoint; SendPoint and PredictPoint never
\* coincide, so sending and predicting are disjoint events.

VARIABLES suspect, timeout, lastSeen, clock, outbox

vars == <<suspect, timeout, lastSeen, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastSeen \in [Proc -> Nat]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastSeen = [p \in Proc |-> 0]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* Send an alive message to every other process whenever the local clock
\* reaches the send interval and is not simultaneously a predict tick.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.dest \in (Proc \ {p})}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastSeen' = [q \in Proc |->
            IF q = p THEN lastSeen[q]
            ELSE IF q \in suspect[p] THEN lastSeen[q]
            ELSE lastSeen[q] + 1]
    /\ UNCHANGED <<suspect, timeout>>

\* Make a crash prediction (add to the suspicion set) whenever the local
\* clock reaches the predict interval and is not simultaneously a send tick.
PredictCrash(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [p \in Proc |->
            suspect[p] \cup {q \in Proc : q # p /\ lastSeen[q] > timeout[p]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastSeen' = [q \in Proc |->
            IF q = p THEN lastSeen[q]
            ELSE IF q \in suspect[p] THEN lastSeen[q]
            ELSE lastSeen[q] + 1]
    /\ UNCHANGED <<timeout, outbox>>

\* At all other times, receive incoming messages and update state.
Receive(p) ==
    /\ clock[p] % SendPoint # 0 \/ clock[p] % PredictPoint # 0
    /\ LET
        recvd == {m \in outbox[p] : m.dest = p}
        newSus == {q \in suspect[p] : \A r \in outbox[q] : r.dest # p}
        newTout == [q \in Proc |->
            IF \E r \in outbox[q] : r.dest = p /\ q \in suspect[p]
                THEN timeout[p] + 1 ELSE timeout[p]]
      IN
        /\ suspect' = [p \in Proc |->
                (suspect[p] \ newSus) \cup newSus]
        /\ timeout' = newTout
        /\ lastSeen' = [q \in Proc |->
                IF q \in suspect[p] THEN 0
                ELSE IF q \in {m.dest \in outbox[p]} THEN 0
                ELSE lastSeen[q]]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] < SendPoint
                                      THEN clock[p] + 1 ELSE 0]

Next == \E p \in Proc : SendAlive(p) \/ PredictCrash(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====