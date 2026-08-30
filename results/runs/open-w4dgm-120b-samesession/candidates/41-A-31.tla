---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,       \* the set of processes
    d0,         \* the default timeout interval
    SendPoint,  \* clock modulus at which a process sends alive messages
    PredictPoint, \* clock modulus at which a process makes predictions
    Messages    \* the type of messages (parameterized)

\* A message is a tagged alive-message from a sender to a receiver
Message == [sender: Proc, receiver: Proc, kind: Messages]

VARIABLES
    suspect,    \* suspect[a]: the set of processes a suspects of having crashed
    timeout,    \* timeout[a][b]: the timeout interval a uses for process b
    lastHeard,  \* lastHeard[a][b]: ticks since a last heard from b
    clock,      \* clock[a]: local clock value for process a
    outbox      \* outbox[a]: set of alive messages a wants to send

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Message]

Init ==
    /\ suspect = [a \in Proc |-> {}]
    /\ timeout = [a \in Proc |-> [b \in Proc |-> d0]]
    /\ lastHeard = [a \in Proc |-> [b \in Proc |-> 0]]
    /\ clock = [a \in Proc |-> 0]
    /\ outbox = [a \in Proc |-> {}]

\* A process sends alive messages when its clock hits the send interval
SendAlive(a) ==
    /\ clock[a] % SendPoint = 0
    /\ clock[a] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![a] =
            { [sender |-> a, receiver |-> b, kind |-> "alive"] : b \in Proc }]
    /\ clock' = [clock EXCEPT ![a] = clock[a] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![a] =
            [b \in Proc |-> IF lastHeard[a][b] >= timeout[a][b]
                            THEN lastHeard[a][b] ELSE lastHeard[a][b] + 1]]
    /\ UNCHANGED <<suspect, timeout>>

\* A process predicts crashes for processes it has not heard from within their timeout
PredictCrash(a) ==
    /\ clock[a] % PredictPoint = 0
    /\ clock[a] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![a] =
            suspect[a] \cup { b \in Proc : lastHeard[a][b] > timeout[a][b] }]
    /\ lastHeard' = [lastHeard EXCEPT ![a] =
            [b \in Proc |-> IF lastHeard[a][b] >= timeout[a][b]
                            THEN lastHeard[a][b] ELSE lastHeard[a][b] + 1]]
    /\ clock' = [clock EXCEPT ![a] = clock[a] + 1]
    /\ UNCHANGED <<timeout, outbox>>

\* A process receives incoming messages, resetting counters and clearing suspicions;
\* a received message from a suspected process expands that process's timeout
ReceiveMsgs(a) ==
    /\ ~(clock[a] % SendPoint = 0 /\ clock[a] % PredictPoint # 0)
    /\ ~(clock[a] % PredictPoint = 0 /\ clock[a] % SendPoint # 0)
    /\ \E m \in outbox[a] \cup { [sender |-> b, receiver |-> a, kind |-> "alive"] : b \in Proc } :
        /\ lastHeard' = [lastHeard EXCEPT ![a][m.sender] = 0]
        /\ suspect' = [suspect EXCEPT ![a] = suspect[a] \ {m.sender}]
        /\ timeout' = [timeout EXCEPT ![a][m.sender] =
                IF m.sender \in suspect[a] THEN timeout[a][m.sender] + 1 ELSE timeout[a][m.sender]]
    /\ outbox' = [outbox EXCEPT ![a] = {}]
    /\ clock' = [clock EXCEPT ![a] =
            IF clock[a] + 1 > SendPoint /\ clock[a] + 1 > PredictPoint
                /\ \A b \in Proc : clock[a] + 1 <= timeout[a][b]
            THEN 0 ELSE clock[a] + 1]

Next ==
    \/ \E a \in Proc : SendAlive(a)
    \/ \E a \in Proc : PredictCrash(a)
    \/ \E a \in Proc : ReceiveMsgs(a)

Spec == Init /\ [][Next]_vars

\* Safety: every component stays within its domain, keeping the model well-typed
TypeOK == TypeOK
====