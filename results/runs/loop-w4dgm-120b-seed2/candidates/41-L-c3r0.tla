---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicionSet, timeout, lastHeard, clock, toSend

vars == <<suspicionSet, timeout, lastHeard, clock, toSend>>

\* toSend is a set of messages, each a (sender, receiver) pair; messages are
\* delivered nondeterministically, so a receive can wake any subset of recipients.
Delivered == { m \in toSend : m.receiver \in Proc }

TypeOK ==
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ suspicionSet \in [Proc -> SUBSET Proc]
    /\ toSend \subseteq [sender: Proc, receiver: Proc]

Init ==
    /\ suspicionSet = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ toSend = {}

SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ toSend' = toSend \cup { [sender |-> p, receiver |-> q] : q \in Proc, q # p }
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |-> IF q \in suspicionSet[p] THEN @ ELSE @ + 1]]
    /\ UNCHANGED <<suspicionSet, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicionSet' = [suspicionSet EXCEPT ![p] =
            @ \cup { q \in Proc : lastHeard[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |-> IF q \in suspicionSet[p] THEN @ ELSE @ + 1]]
    /\ UNCHANGED <<timeout, toSend>>

Receive(p) ==
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ clock[p] <= 2 * SendPoint
    /\ clock' = [clock EXCEPT ![p] = IF @ + 1 > 2 * SendPoint THEN 0 ELSE @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] =
            [q \in Proc |-> IF \E m \in Delivered : m.sender = q THEN 0 ELSE @ + 1]]
    /\ suspicionSet' = [suspicionSet EXCEPT ![p] =
            { q \in Proc : lastHeard[p][q] <= timeout[p][q] }]
    /\ timeout' = [timeout EXCEPT ![p] =
            [q \in Proc |-> IF q \in suspicionSet[p] /\ q \in { m.sender : m \in Delivered }
                           THEN @ + 1 ELSE @]]
    /\ toSend' = toSend \ Delivered

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

Spec == Init /\ [][Next]_vars

====