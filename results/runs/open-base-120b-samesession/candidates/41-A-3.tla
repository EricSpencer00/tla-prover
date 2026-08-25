---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (Nat)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    clock,        \* [Proc -> Nat]   local clocks
    suspicion,    \* [Proc -> SUBSET Proc]   current suspicion sets
    timeout,      \* [Proc -> [Proc -> Nat]]   timeout intervals per target
    lastHeard,    \* [Proc -> [Proc -> Nat]]   ticks since last alive received
    outbox        \* [Proc -> SUBSET Messages]   messages to be sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* The set of all alive messages a process p can generate
AliveMsgs(p) == 
    { [type |-> "alive", from |-> p, to |-> q] : q \in Proc \ {p} }

\* Increment lastHeard counters for those not yet timed‑out
IncLast(p, lh) == 
    [q \in Proc |-> 
        IF lh[p][q] < timeout[p][q] 
        THEN lh[p][q] + 1 
        ELSE lh[p][q]]

\* Maximum timeout value observed by a process p
MaxTimeout(p) == 
    IF Proc = {} THEN 0 
    ELSE Max({ timeout[p][q] : q \in Proc })

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Send(p) ==
    /\ (clock[p] % SendPoint) = 0
    /\ (clock[p] % PredictPoint) # 0          \* not a predict tick
    /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \cup AliveMsgs(p)]
    /\ suspicion' = suspicion
    /\ timeout' = timeout
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncLast(p, lastHeard)]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED << clock, suspicion, timeout, lastHeard >> \* for other processes

Predict(p) ==
    /\ (clock[p] % PredictPoint) = 0
    /\ (clock[p] % SendPoint) # 0            \* not a send tick
    /\ let NewSuspects == { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup NewSuspects]
    /\ outbox' = outbox
    /\ timeout' = timeout
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncLast(p, lastHeard)]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED << clock, suspicion, timeout, lastHeard >> \* for other processes

Receive(p) ==
    /\ \E R \subseteq Proc \ {p} : 
        /\ outbox' = outbox
        /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
        /\ lastHeard' = [lastHeard EXCEPT ![p] = 
            [q \in Proc |-> 
                IF q \in R 
                THEN 0 
                ELSE lastHeard[p][q] + 1]]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ R]
        /\ timeout' = [timeout EXCEPT ![p] =
            [q \in Proc |-> 
                IF q \in R /\ q \in suspicion[p] 
                THEN timeout[p][q] + 1 
                ELSE timeout[p][q]]]

ResetClock(p) ==
    /\ clock[p] > Max({SendPoint, PredictPoint, MaxTimeout(p)})
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED << suspicion, timeout, lastHeard, outbox >>

Next ==
    \E p \in Proc :
        Send(p) \/ Predict(p) \/ Receive(p) \/ ResetClock(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<clock, suspicion, timeout, lastHeard, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Properties (currently only the type invariant)
\* ----------------------------------------------------------------------
Properties == []TypeOK

====