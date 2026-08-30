---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,     \* the set of processes
    d0,       \* default timeout interval
    SendPoint,    \* local-clock interval at which a process sends alive messages
    PredictPoint, \* local-clock interval at which a process makes predictions
    Messages  \* the set of alive-message types (each addressed-to-one process)

VARIABLES
    suspect,    \* suspect[p]: set of processes p suspects have crashed
    timeout,    \* timeout[p]: [Proc -> Nat] adaptive timeout intervals p uses
    lastHeard,  \* lastHeard[p]: [Proc -> Nat] clock ticks since p last heard from each q
    clock,      \* clock[p]: p's local clock
    outbox      \* outbox[p]: set of alive messages p intends to send this transition

vars == <<suspect, timeout, lastHeard, clock, outbox>>

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> Nat]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock \in [Proc -> Nat]
    /\ outbox \in [Proc -> SUBSET Messages]

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> d0]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock = [p \in Proc |-> 0]
    /\ outbox = [p \in Proc |-> {}]

\* Sending and predicting never coincide because SendPoint and PredictPoint are
\* positive and not multiples of each other.
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { m \in Messages : m # p }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p] = [q \in Proc |->
                            IF q \in outbox[p] /\ q \notin suspect[p]
                                THEN lastHeard[p][q]
                                ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<suspect, timeout>>

MakePrediction(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
                        { q \in Proc : lastHeard[p][q] > timeout[p] }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p] = [q \in Proc |->
                            IF q \in outbox[p] /\ q \notin suspect[p]
                                THEN lastHeard[p][q]
                                ELSE lastHeard[p][q] + 1]]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p, s, msg) ==
    /\ msg \in outbox[s]
    /\ p = msg
    /\ lastHeard' = [lastHeard EXCEPT ![p][s] = 0]
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {s}]
    /\ timeout' = [timeout EXCEPT ![p] = IF s \in suspect[p] THEN @ + 1 ELSE @]
    /\ outbox' = [outbox EXCEPT ![s] = @ \ {msg}]
    /\ UNCHANGED clock

ResetClock(p) ==
    /\ clock[p] > 0
    /\ clock[p] > SendPoint
    /\ clock[p] > PredictPoint
    /\ \A q \in Proc : clock[p] > timeout[p]
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED <<suspect, timeout, lastHeard, outbox>>

Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : MakePrediction(p)
    \/ \E p \in Proc, s \in Proc, msg \in Messages : Receive(p, s, msg)
    \/ \E p \in Proc : ResetClock(p)

Spec == Init /\ [][Next]_vars

====