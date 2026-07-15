---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be instantiated in the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive send interval
    PredictPoint,  \* Positive predict interval, not a multiple of SendPoint
    Messages       \* Set of possible alive messages

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Other(p) == Proc \ {p}

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,    \* [p \in Proc |-> SUBSET Proc] – processes p suspects
    timeout,      \* [p \in Proc |-> [q \in Proc -> Nat]] – timeout intervals
    lastHeard,    \* [p \in Proc |-> [q \in Proc -> Nat]] – ticks since last alive
    clock,        \* [p \in Proc |-> Nat] – local clock
    outbox        \* [p \in Proc |-> SUBSET Messages] – messages to send

\* ----------------------------------------------------------------------
\* Type predicate (used for the TypeOK invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AtSend(p)    == /\ clock[p] % SendPoint = 0
                /\ clock[p] % PredictPoint # 0

AtPredict(p) == /\ clock[p] % PredictPoint = 0
                /\ clock[p] % SendPoint # 0

IsSending(p)   == AtSend(p)
IsPredicting(p) == AtPredict(p)

NonSpecial(p) == ~IsSending(p) /\ ~IsPredicting(p)

MaxTimeout(p) == 
    LET vals == { timeout[p][q] : q \in Proc } IN
    IF vals = {} THEN 0 ELSE Max(vals)

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ IsSending(p)
    /\ outbox' = [ outbox EXCEPT ![p] = { "alive_" \o p \o "_" \o q : q \in Other(p) } ]
    /\ lastHeard' = [ lastHeard EXCEPT 
                        ![p][q] = IF timeout[p][q] # 0 
                                   THEN @ + 1 
                                   ELSE @ 
                        \* increment counters for all q (including self, harmless) \*]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ IsPredicting(p)
    /\ suspicion' = [ suspicion EXCEPT 
                        ![p] = suspicion[p] \cup 
                                 { q \in Proc : lastHeard[p][q] > timeout[p][q] } ]
    /\ lastHeard' = [ lastHeard EXCEPT ![p][q] = @ + 1 ]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ UNCHANGED <<outbox, timeout>>

Receive(p) ==
    /\ NonSpecial(p)
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ lastHeard' = [ lastHeard EXCEPT ![p][q] = IF "alive_" \o q \o "_" \o p \in outbox[q]
                                                THEN 0
                                                ELSE @ + 1
                      \* for every q, either reset or increment \*]
    /\ suspicion' = [ suspicion EXCEPT ![p] = suspicion[p] \ { 
                        q \in Proc : "alive_" \o q \o "_" \o p \in outbox[q] } ]
    /\ timeout' = [ timeout EXCEPT ![p][q] = 
                        IF q \in suspicion[p] /\ "alive_" \o q \o "_" \o p \in outbox[q]
                        THEN @ + 1
                        ELSE @ ]
    /\ clock' = [clock EXCEPT ![p] = 
                        IF @ + 1 > SendPoint /\ @ + 1 > PredictPoint /\
                           @ + 1 > MaxTimeout(p)
                        THEN 0
                        ELSE @ + 1]

\* ----------------------------------------------------------------------
\* Composite next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox>>

=============================================================================