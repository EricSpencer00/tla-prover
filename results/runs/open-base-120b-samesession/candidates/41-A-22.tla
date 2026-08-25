---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Proc,        \* Set of process identifiers
    d0,          \* Default timeout value (positive integer)
    SendPoint,   \* Positive integer: send interval
    PredictPoint,\* Positive integer: predict interval (not a multiple of SendPoint)
    Messages     \* Set of possible messages (records with fields type, from, to)

VARIABLES 
    clock,       \* [Proc -> Nat]  local clocks
    timeout,     \* [Proc -> [Proc -> Nat]]  timeout intervals per pair
    last,        \* [Proc -> [Proc -> Nat]]  ticks since last heard per pair
    suspicion,   \* [Proc -> SUBSET Proc]   current suspicion sets
    outbox       \* [Proc -> SUBSET Messages]   messages a process intends to send

\*=====================================================================
\* Helper definitions
\*=====================================================================

\* Increment all last‑heard counters of process p (except to itself)
LastInc(p) == 
    [q \in Proc |-> IF q # p THEN last[p][q] + 1 ELSE last[p][q]]

\* Reset counters for a set S of senders and increment the others
LastReset(p, S) ==
    [q \in Proc |-> 
        IF q \in S THEN 0
        ELSE IF q # p THEN last[p][q] + 1
        ELSE last[p][q]]

\* Adaptive timeout increase for a set S of senders that are currently suspected
TimeoutInc(p, S) ==
    [q \in Proc |-> 
        IF q \in S /\ q \in suspicion[p] THEN timeout[p][q] + 1
        ELSE timeout[p][q]]

\*=====================================================================
\* Initialization
\*=====================================================================

Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q # p THEN d0 ELSE 0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ suspicion = [p \in Proc |-> {}]
    /\ outbox = [p \in Proc |-> {}]

\*=====================================================================
\* Actions for a single process p
\*=====================================================================

Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = 
                    { [type |-> "alive", from |-> p, to |-> q] : q \in Proc \ {p} }]
    /\ timeout' = timeout
    /\ suspicion' = suspicion
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ last' = [last EXCEPT ![p] = LastInc(p)]

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ let newSus == { q \in Proc \ {p} : last[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ timeout' = timeout
    /\ outbox' = outbox
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ last' = [last EXCEPT ![p] = LastInc(p)]

Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0) 
    /\ ~(clock[p] % PredictPoint = 0)
    /\ \E S \subseteq Proc \ {p} :
         /\ outbox' = outbox
         /\ clock' = [clock EXCEPT ![p] = @ + 1]
         /\ last' = [last EXCEPT ![p] = LastReset(p, S)]
         /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ S]
         /\ timeout' = [timeout EXCEPT ![p] = TimeoutInc(p, S)]

\*=====================================================================
\* Next-state relation (one process makes a step)
\*=====================================================================

Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\*=====================================================================
\* Specification
\*=====================================================================

Spec == Init /\ [] [Next]_<<clock, timeout, last, suspicion, outbox>>

\*=====================================================================
\* Invariant: type correctness
\*=====================================================================

TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Messages]

\*=====================================================================
\* Additional required identifiers
\*=====================================================================

Init == Init
Next == Next
SPECIFICATION == Spec
INVARIANTS == TypeOK
PROPERTIES == TRUE

====