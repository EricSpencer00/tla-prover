---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer send interval
    PredictPoint,  \* Positive integer predict interval
    Messages       \* Set of messages (provided by the environment)

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   -- suspected processes
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout per pair
    last,        \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive
    clock,       \* [p \in Proc |-> Nat]                     -- local clock
    out          \* [p \in Proc |-> SUBSET Messages]        -- outgoing msgs

\* ----------------------------------------------------------------------
\* Helper definitions
\* Message record for an alive ping
MessageAlive(p,q) == [type |-> "alive", from |-> p, to |-> q]

\* The set of all other processes (excluding self)
Other(p) == Proc \ {p}

\* Increment a counter unless it has already reached (or exceeded) its timeout
IncIfNotTimedOut(cnt, to) ==
    IF cnt < to THEN cnt + 1 ELSE cnt

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last      = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ out       = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send-alive action
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ \* Create an alive message for every other process
       out' = [out EXCEPT ![p] = out[p] \cup { MessageAlive(p,q) : q \in Other(p) }]
    /\ \* Advance the local clock
       clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ \* Increment last‑heard counters for those not yet timed‑out
       last' = [last EXCEPT ![p][q] = IncIfNotTimedOut(last[p][q], timeout[p][q])
                                   \* for all q \in Proc
                                   \* (the EXCEPT construct updates all q)
                ]
    /\ UNCHANGED <<suspicion, timeout>>

\* ----------------------------------------------------------------------
\* Predict (suspicion) action
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ \* Suspect any process whose last‑heard exceeds its timeout
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
                     { q \in Other(p) : last[p][q] > timeout[p][q] }]
    /\ \* Increment all last‑heard counters
       last' = [last EXCEPT ![p][q] = last[p][q] + 1
                                   \* for all q \in Proc
                ]
    /\ \* Advance the clock
       clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<out, timeout>>

\* ----------------------------------------------------------------------
\* Receive action (any clock value not triggering send or predict)
Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \* Nondeterministically choose a set of alive messages that arrive
       \* (each identified by its sender)
       \* recSet ⊆ Other(p)
       \E recSet \in SUBSET Other(p) :
          /\ \* Update last‑heard counters:
             last' = [last EXCEPT ![p][q] = IF q \in recSet
                                                THEN 0
                                                ELSE IF last[p][q] < timeout[p][q]
                                                     THEN last[p][q] + 1
                                                     ELSE last[p][q]
                     ]
          /\ \* Remove any sender that responded from suspicion
             suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ setdiff recSet]
          /\ \* Adaptive timeout increase for suspected senders
             timeout' = [timeout EXCEPT ![p][q] = IF q \in recSet /\ q \in suspicion[p]
                                                   THEN timeout[p][q] + 1
                                                   ELSE timeout[p][q]
                        ]
          /\ \* Advance the clock (reset to 0 if it exceeds all thresholds – simplified)
             clock' = [clock EXCEPT ![p] = clock[p] + 1]
             /\ UNCHANGED out

\* ----------------------------------------------------------------------
\* The next-state relation aggregates the three actions for any process
Next ==
    \E p \in Proc : \/ Send(p)
                     \/ Predict(p)
                     \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ last      \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ out       \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : p \notin suspicion[p]   \* a process never suspects itself

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<suspicion, timeout, last, clock, out>>

\* ----------------------------------------------------------------------
\* Properties (placeholder – can be extended by the user)
Properties == Spec

=============================================================================