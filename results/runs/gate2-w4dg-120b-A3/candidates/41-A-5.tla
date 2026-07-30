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
    outgoing

vars == <<suspicion, timeout, lastHeard, clock, outgoing>>

NoMsg == [sender |-> "noone", target |-> "noone"]
Current(msgs) == CHOOSE m \in msgs : TRUE
MaxTime(p) ==
    LET s == {clock[p] : p \in Proc} \cup
             {d0} \cup
             {timeout[p][q] : q \in (Proc \ {p})}
    IN
    IF \E x \in s : TRUE THEN LET y == CHOOSE x \in s : TRUE IN y ELSE 0

TypeOK ==
    /\ \A p \in Proc : lastHeard[p] \in [Proc -> Nat]
    /\ \A p \in Proc : timeout[p] \in [Proc -> Nat]
    /\ \A p \in Proc : suspicion[p] \subseteq Proc
    /\ \A p \in Proc : clock[p] \in Nat
    /\ \A p \in Proc : outgoing[p] \subseteq Messages

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {NoMsg}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] =
                        [x \in Proc |-> [sender |-> p, target |-> x]]]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF q = p \/ lastHeard[p][q] >= timeout[p][q]
                            THEN lastHeard[p][q]
                            ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] =
                        suspicion[p] \cup
                        {q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF lastHeard[p][q] >= timeout[p][q]
                            THEN lastHeard[p][q]
                            ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outgoing>>

Receive(p) ==
    /\ outgoing' = [outgoing EXCEPT ![p] = {NoMsg}]
    /\ suspicion' = [suspicion EXCEPT ![p] =
                        {q \in suspicion[p] :
                            \A m \in outgoing[p] : m.target # q}]
    /\ timeout' = [timeout EXCEPT ![p] = [q \in Proc \ {p} |-> IF
                        (\E m \in outgoing[p] : m.target = q)
                        THEN @ + 1
                        ELSE @]]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = [q \in Proc |->
                        IF q \in {m.target : m \in outgoing[p]}
                        THEN 0
                        ELSE IF lastHeard[p][q] >= timeout[p][q]
                        THEN lastHeard[p][q]
                        ELSE lastHeard[p][q] + 1]]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > MaxTime(p) THEN 0 ELSE clock[p] + 1]

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====