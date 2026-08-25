---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Positive integer: period for sending alive messages
    PredictPoint,  \* Positive integer: period for making predictions
    Messages       \* Set of all possible messages (used for type checking)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    Suspect,   \* [p \in Proc |-> SUBSET Proc]  -- suspicion set of each process
    Timeout,   \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout for each pair
    LastHeard, \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive from q to p
    Clock,     \* [p \in Proc |-> Nat]                     -- local logical clock
    Outbox     \* [p \in Proc |-> SUBSET Messages]        \* messages a process intends to send

vars == << Suspect, Timeout, LastHeard, Clock, Outbox >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsSendTime(p) == (Clock[p] % SendPoint = 0) /\ (Clock[p] % PredictPoint # 0)
IsPredictTime(p) == (Clock[p] % PredictPoint = 0) /\ (Clock[p] % SendPoint # 0)

\* Alive message constructor (record) – the concrete shape of a message is left
\* abstract; only its membership in the constant set Messages is required.
AliveMsg(p,q) == [type |-> "alive", from |-> p, to |-> q]

\* The set of processes other than p
OtherProcs(p) == Proc \ {p}

\* Increment counters for a given process p, respecting its current timeout
IncCounters(p, lh) ==
    [ q \in Proc |-> 
        IF lh[p][q] < Timeout[p][q] THEN lh[p][q] + 1 ELSE lh[p][q] ]

\* Reset the local clock to 0 when it exceeds the largest relevant period.
ResetClock(c) ==
    IF c + 1 > Max({SendPoint, PredictPoint}) THEN 0 ELSE c + 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Suspect = [p \in Proc |-> {}]
    /\ Timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ LastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock = [p \in Proc |-> 0]
    /\ Outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ IsSendTime(p)
    /\ \* create alive messages addressed to every other process
       Outbox' = [Outbox EXCEPT ![p] = { AliveMsg(p,q) : q \in OtherProcs(p) }]
    /\ \* advance the local clock
       Clock' = [Clock EXCEPT ![p] = ResetClock(Clock[p])]
    /\ \* increment last‑heard counters for processes not yet timed‑out
       LastHeard' = [LastHeard EXCEPT ![p] = IncCounters(p, LastHeard)]
    /\ \* other variables remain unchanged
       Suspect' = Suspect
       Timeout' = Timeout

Predict(p) ==
    /\ IsPredictTime(p)
    /\ \* add to suspicion any process whose counter exceeds its timeout
       Suspect' = [Suspect EXCEPT ![p] = 
                     Suspect[p] \cup 
                     { q \in OtherProcs(p) : LastHeard[p][q] > Timeout[p][q] }]
    /\ \* increment all counters
       LastHeard' = [LastHeard EXCEPT ![p] = 
                       [ q \in Proc |-> LastHeard[p][q] + 1 ]]
    /\ \* advance the local clock
       Clock' = [Clock EXCEPT ![p] = ResetClock(Clock[p])]
    /\ \* other variables unchanged
       Outbox' = Outbox
       Timeout' = Timeout

\* Receive action models the effect of receiving any subset of alive messages.
\* The environment supplies, nondeterministically, the set Rcv(p) of senders
\* whose alive messages are received by p in the current step.
Receive(p) ==
    LET Rcv == { q \in OtherProcs(p) : 
                  \* nondeterministically decide whether an alive from q is received
                  CHOOSE b \in BOOLEAN : b } IN
    /\ \* Update suspicion: remove any sender that is heard from
       Suspect' = [Suspect EXCEPT ![p] = Suspect[p] \ Rcv]
    /\ \* Reset last‑heard counters for heard‑from processes,
       \* increment counters for the rest
       LastHeard' = [LastHeard EXCEPT ![p][q] = 
                       IF q \in Rcv THEN 0 ELSE LastHeard[p][q] + 1 
                       \* for all q \in Proc
                     ]
    /\ \* Adaptive timeout increase for processes that were suspected and
       \* whose alive message arrived
       Timeout' = [Timeout EXCEPT ![p][q] = 
                     IF q \in Rcv /\ q \in Suspect[p] 
                     THEN Timeout[p][q] + 1 
                     ELSE Timeout[p][q] ]
    /\ \* Advance (and possibly wrap) the clock
       Clock' = [Clock EXCEPT ![p] = ResetClock(Clock[p])]
    /\ \* Outbox unchanged
       Outbox' = Outbox

\* The overall Next relation
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Suspect \in [Proc -> SUBSET Proc]
    /\ Timeout \in [Proc -> [Proc -> Nat]]
    /\ LastHeard \in [Proc -> [Proc -> Nat]]
    /\ Clock \in [Proc -> Nat]
    /\ Outbox \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : \A q \in Proc :
          /\ Timeout[p][q] >= d0
          /\ LastHeard[p][q] >= 0

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Theorem (optional) that the type invariant is always maintained
\* ----------------------------------------------------------------------
THEOREM TypeInvariant == Spec => []TypeOK

====