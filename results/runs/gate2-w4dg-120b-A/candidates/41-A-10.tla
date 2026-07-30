---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,
    d0,
    SendPoint,
    PredictPoint,
    Messages

ASSUME SendPoint > 0 /\ PredictPoint > 0 /\ SendPoint % PredictPoint # 0 /\ PredictPoint % SendPoint # 0

VARIABLES
    suspect,
    timeout,
    lastHeard,
    clock,
    outgoing

vars == <<suspect, timeout, lastHeard, clock, outgoing>>

SomeMsg == CHOOSE m \in Messages : TRUE

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = {SomeMsg}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = @ \cup {q \in Proc : lastHeard[p][q] > timeout[p][q]}]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |-> IF q = p \/ lastHeard[p][q] >= timeout[p][q] THEN @ ELSE @ + 1]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
    /\ \E m \in outgoing[p] :
         /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                            IF m.q = q /\ m.from \notin suspect[p]
                                THEN 0
                                ELSE IF m.from \in suspect[p] \/ m.from = p
                                    THEN LET t == timeout[p][m.q] IN IF t < d0 + 1 THEN t + 1 ELSE t
                                    ELSE @]]
         /\ suspect' = [suspect EXCEPT ![p] = {q \in suspect[p] : q # m.q}]
    /\ outgoing' = [outgoing EXCEPT ![p] = {}]
    /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\ @ + 1 > d0 + 1 THEN 0 ELSE @ + 1]
    /\ UNCHANGED timeout

Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

TypeOK ==
    /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : suspect[p] \subseteq Proc
    /\ \A p \in Proc : outgoing[p] \subseteq Messages

====