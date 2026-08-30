---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outbox

vars == <<suspicion, timeout, lastHeard, clock, outbox>>

RECURSIVE SumOf(_, _)
SumOf(f, S) ==
    IF S = {} THEN 0
    ELSE LET x == CHOOSE y \in S : TRUE
         IN f[x] + SumOf(f, S \ {x})

Bound == SumOf(timeout, Proc)

TypeOK ==
    /\ \A p \in Proc : lastHeard[p] \in Nat
    /\ \A p \in Proc : timeout[p] \in Nat
    /\ \A p \in Proc : suspicion[p] \subseteq Proc
    /\ \A p \in Proc : clock[p] \in Nat
    /\ \A p \in Proc : outbox[p] \subseteq Messages

Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = {m \in Messages : m.from = p}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF q \in suspicion[p] THEN lastHeard[p][q]
                            ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] =
                        suspicion[p] \cup {q \in Proc : lastHeard[p][q] > timeout[p]}]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
                        [q \in Proc |->
                            IF q \in suspicion[p] THEN lastHeard[p][q]
                            ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ clock[p] <= Bound
    /\ \E m \in outbox[p] :
        /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {m.from}]
        /\ timeout' = [timeout EXCEPT ![m.from] =
                            IF m.from \in suspicion[p] THEN timeout[m.from] + 1 ELSE timeout[m.from]]
        /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \ {m}]
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] > Max(clock) THEN 0 ELSE clock[p] + 1]

Next == \E p \in Proc :
    SendAlive(p) \/ Predict(p) \/ Receive(p)

Spec == Init /\ [][Next]_vars

====