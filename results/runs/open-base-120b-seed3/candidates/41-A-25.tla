---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    Suspect,      \* [p \in Proc |-> SUBSET Proc]   -- suspicion set of each process
    Timeout,      \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- timeout intervals
    LastHeard,    \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive from q
    Clock,        \* [p \in Proc |-> Nat]                     -- local logical clock
    Net           \* SUBSET Messages                          \* messages in transit

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
SendCond(p)    == (Clock[p] % SendPoint = 0) /\ (Clock[p] % PredictPoint # 0)
PredictCond(p) == (Clock[p] % PredictPoint = 0) /\ (Clock[p] % SendPoint # 0)

AliveMsg(p, q) == [src |-> p, dst |-> q, type |-> "alive"]

AllOther(p)   == Proc \ {p}

\* ----------------------------------------------------------------------
\* Initial predicate
\* ----------------------------------------------------------------------
Init == 
    /\ Suspect   = [p \in Proc |-> {}]
    /\ Timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ LastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock     = [p \in Proc |-> 0]
    /\ Net       = {}

\* ----------------------------------------------------------------------
\* Action: Send alive messages
\* ----------------------------------------------------------------------
SendAlive(p) == 
    LET newMsgs == { AliveMsg(p, q) : q \in AllOther(p) } IN
    /\ SendCond(p)
    /\ Suspect'   = Suspect
    /\ Timeout'   = Timeout
    /\ Net'       = Net \cup newMsgs
    /\ Clock'     = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ LastHeard' = [LastHeard EXCEPT 
                        ![p][q] = IF q \in AllOther(p) 
                                   THEN LastHeard[p][q] + 1 
                                   ELSE @ ]

\* ----------------------------------------------------------------------
\* Action: Make predictions (update suspicion set)
\* ----------------------------------------------------------------------
Predict(p) ==
    LET newSuspects == { q \in AllOther(p) : LastHeard[p][q] > Timeout[p][q] } IN
    /\ PredictCond(p)
    /\ Suspect'   = [Suspect EXCEPT ![p] = Suspect[p] \cup newSuspects]
    /\ Timeout'   = Timeout
    /\ Net'       = Net
    /\ Clock'     = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ LastHeard' = [LastHeard EXCEPT 
                        ![p][q] = IF q \in AllOther(p) 
                                   THEN LastHeard[p][q] + 1 
                                   ELSE @ ]

\* ----------------------------------------------------------------------
\* Action: Receive incoming alive messages
\* ----------------------------------------------------------------------
Receive(p) ==
    LET incoming   == { m \in Net : m.dst = p /\ m.type = "alive" } 
        senders    == { m.src : m \in incoming } 
        newSuspect == Suspect[p] \ senders 
        updTimeout == [q \in Proc |-> 
                         IF q \in senders /\ q \in Suspect[p] 
                         THEN Timeout[p][q] + 1 
                         ELSE Timeout[p][q] ] 
        updLast    == [q \in Proc |-> 
                         IF q \in senders 
                         THEN 0 
                         ELSE LastHeard[p][q] + 1 ] 
    IN
    /\ ~SendCond(p) /\ ~PredictCond(p)   \* all other clock values
    /\ Suspect'   = [Suspect EXCEPT ![p] = newSuspect]
    /\ Timeout'   = [Timeout EXCEPT ![p] = updTimeout]
    /\ Net'       = Net \ incoming
    /\ Clock'     = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ LastHeard' = [LastHeard EXCEPT ![p] = updLast]

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving of process actions)
\* ----------------------------------------------------------------------
Next == 
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Suspect   \in [Proc -> SUBSET Proc]
    /\ Timeout   \in [Proc -> [Proc -> Nat]]
    /\ LastHeard \in [Proc -> [Proc -> Nat]]
    /\ Clock     \in [Proc -> Nat]
    /\ Net       \subseteq Messages

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Suspect, Timeout, LastHeard, Clock, Net>>

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
INIT Init
NEXT Next
INVARIANT TypeOK

====