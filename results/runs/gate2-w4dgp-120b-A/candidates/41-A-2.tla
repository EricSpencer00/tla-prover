---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES locTime, suspect, timeout, lastHeard, outbox

vars == <<locTime, suspect, timeout, lastHeard, outbox>>

\* An eventually perfect failure detector: processes send alive messages and
\* predict crashes independently, based on an adaptive timeout per peer.
\* send and predict clocks never coincide (the non-divisibility constraint),
\* so no action is starved by the other.

TypeOK ==
    /\ lastHeard \in [Proc -> Nat]
    /\ timeout \in [Proc -> Nat]
    /\ suspect \subseteq Proc
    /\ locTime \in Nat
    /\ outbox \subseteq Messages

Init ==
    /\ suspect = {}
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> 0]
    /\ locTime = 0
    /\ outbox = {}

SendAlive ==
    /\ locTime % SendPoint = 0
    /\ locTime % PredictPoint # 0
    /\ outbox' = {m \in Messages : m.receiver = "self"}
    /\ locTime' = locTime + 1
    /\ lastHeard' = [p \in Proc |-> IF p = "self" THEN lastHeard[p]
                                     ELSE IF lastHeard[p] < timeout[p]
                                          THEN lastHeard[p] + 1 ELSE timeout[p]]
    /\ UNCHANGED <<suspect, timeout>>

Predict ==
    /\ locTime % PredictPoint = 0
    /\ locTime % SendPoint # 0
    /\ suspect' = suspect \cup {p \in Proc : p # "self" /\ lastHeard[p] > timeout[p]}
    /\ locTime' = locTime + 1
    /\ lastHeard' = [p \in Proc |-> IF p = "self" THEN lastHeard[p]
                                     ELSE IF lastHeard[p] < timeout[p]
                                          THEN lastHeard[p] + 1 ELSE timeout[p]]
    /\ UNCHANGED <<timeout, outbox>>

\* Receiving an alive message resets the timer and clears suspicion; a message
\* from a suspected process causes that process's timeout to grow.
Receive ==
    /\ locTime' = IF locTime + 1 > SendPoint /\ locTime + 1 > PredictPoint
                  /\ \A p \in Proc : locTime + 1 > timeout[p]
                  THEN 0 ELSE locTime + 1
    /\ suspect' = suspect \ {[m.receiver] \in outbox}
    /\ lastHeard' = [p \in Proc |->
                        IF [receiver |-> p] \in outbox THEN 0
                        ELSE IF p = "self" THEN lastHeard[p]
                        ELSE IF lastHeard[p] < timeout[p]
                             THEN lastHeard[p] + 1 ELSE timeout[p]]
    /\ timeout' = [p \in Proc |->
                        IF [receiver |-> p] \in outbox /\ p \in suspect
                        THEN timeout[p] + 1 ELSE timeout[p]]
    /\ UNCHANGED outbox

Next == SendAlive \/ Predict \/ Receive

Spec == Init /\ [][Next]_vars

====