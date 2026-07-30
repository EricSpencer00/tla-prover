---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

NONE == "none"
MaxT == 2
MaxI == 2
MaxL == 2

VARIABLES
    suspected,
    deadline,
    lastHeard,
    clock,
    outbox

vars == <<suspected, deadline, lastHeard, clock, outbox>>

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> 0..MaxT]]
    /\ deadline \in [Proc -> [Proc -> 0..MaxI]]
    /\ suspected \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : clock[p] \in 0..MaxL

Init ==
    /\ \A p \in Proc :
         /\ suspected[p] = {}
         /\ deadline[p] = [q \in Proc |-> d0]
         /\ lastHeard[p] = [q \in Proc |-> 0]
         /\ clock[p] = 0
         /\ outbox[p] = {}

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ clock[p] <= MaxL
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p /\ m.to \in Proc}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q \in suspected[p] THEN @ - 1 ELSE @ + 1]]
    /\ UNCHANGED <<suspected, deadline>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ clock[p] <= MaxL
    /\ suspected' = [suspected EXCEPT ![p] = @ \cup {q \in Proc :
                        lastHeard[p][q] > deadline[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q \in suspected[p] THEN @ - 1 ELSE @ + 1]]
    /\ UNCHANGED <<deadline, outbox>>

Receive(p) ==
    /\ clock[p] <= MaxL
    /\ \E m \in outbox[p] :
         /\ lastHeard' = [lastHeard EXCEPT ![p][m.to] = 0]
         /\ suspected' = [suspected EXCEPT ![p] = @ \ {m.to}]
         /\ deadline' = [deadline EXCEPT ![p][m.to] = IF m.to \in suspected[p] AND @ < MaxI THEN @ + 1 ELSE @]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxL THEN 0 ELSE clock[p] + 1]

Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

Spec == Init /\ [][Next]_vars

====