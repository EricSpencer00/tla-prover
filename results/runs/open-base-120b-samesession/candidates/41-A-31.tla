---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\* ----------------------------------------------------------------------
\* CONSTANTS (instantiated by the TLC configuration)
\* ----------------------------------------------------------------------
CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,  \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages       \* Set of all possible messages (alive messages are a subset)

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES 
    Suspects,   \* [p \in Proc |-> SUBSET Proc]   -- suspicion set of each process
    Timeout,    \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout per pair
    LastHeard,  \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive
    Clock,      \* [p \in Proc |-> Nat]                    -- local clock of each process
    Outgoing    \* [p \in Proc |-> SUBSET Messages]       \* messages a process will send

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveMessage(p, q) == 
    [type |-> "Alive", src |-> p, dst |-> q]

AllAlive(p) == { AliveMessage(p, q) : q \in Proc \ {p} } \cap Messages

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Suspects = [p \in Proc |-> {}]
    /\ Timeout  = [p \in Proc |-> [q \in Proc |-> 
                        IF q = p THEN 0 ELSE d0]]
    /\ LastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock    = [p \in Proc |-> 0]
    /\ Outgoing  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send‑alive action
\* ----------------------------------------------------------------------
Send(p) ==
    /\ p \in Proc
    /\ Clock[p] % SendPoint = 0
    /\ Clock[p] % PredictPoint # 0                \* send and predict never coincide
    /\ 
       \* generate alive messages for every other process
       let newMsgs == AllAlive(p) in
         /\ Outgoing' = [Outgoing EXCEPT ![p] = Outgoing[p] \cup newMsgs]
    /\ 
       \* increment clock
       Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ 
       \* increment last‑heard counters for processes not currently suspected
       LastHeard' = [LastHeard EXCEPT 
                        ![p][q] = IF q # p /\ q \notin Suspects[p] 
                                   THEN LastHeard[p][q] + 1 
                                   ELSE LastHeard[p][q] 
                     \* for all other processes keep the same
                     ]
    /\ UNCHANGED <<Suspects, Timeout>>

\* ----------------------------------------------------------------------
\* Predict (suspicion) action
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ p \in Proc
    /\ Clock[p] % PredictPoint = 0
    /\ Clock[p] % SendPoint # 0
    /\ 
       \* any process whose last‑heard exceeds its timeout becomes suspected
       let newlySuspected == 
            { q \in Proc \ {p} : LastHeard[p][q] > Timeout[p][q] } in
         /\ Suspects' = [Suspects EXCEPT ![p] = Suspects[p] \cup newlySuspected]
    /\ 
       \* increment all last‑heard counters
       LastHeard' = [LastHeard EXCEPT ![p][q] = LastHeard[p][q] + 1 
                                          \* for every q (including p)
                     ]
    /\ Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ UNCHANGED <<Timeout, Outgoing>>

\* ----------------------------------------------------------------------
\* Receive action (abstract – actual message delivery handled externally)
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Proc
    /\ 
       \* No concrete channel is modeled here; this action simply
       \* allows the system to progress when neither send nor predict
       \* conditions hold.  In a full model the controller would update
       \* LastHeard, Suspects and Timeout according to received alive
       \* messages and the adaptive‑timeout rule.
       TRUE
    /\ UNCHANGED <<Suspects, Timeout, LastHeard, Clock, Outgoing>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Suspects \in [Proc -> SUBSET Proc]
    /\ Timeout  \in [Proc -> [Proc -> Nat]]
    /\ LastHeard \in [Proc -> [Proc -> Nat]]
    /\ Clock    \in [Proc -> Nat]
    /\ Outgoing  \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification (used by the .cfg file)
\* ----------------------------------------------------------------------
SPECIFICATION ==
    Init /\ [][Next]_<<Suspects, Timeout, LastHeard, Clock, Outgoing>>

\* ----------------------------------------------------------------------
\* Explicitly exported identifiers (required by the .cfg)
\* ----------------------------------------------------------------------
Init == Init
Next == Next
TypeOK == TypeOK
SPECIFICATION == SPECIFICATION
PROPERTIES == TRUE

====