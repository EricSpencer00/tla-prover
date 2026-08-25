---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Proc,           \* Set of process identifiers
    d0,             \* Default timeout value (positive integer)
    SendPoint,      \* Send interval (positive integer)
    PredictPoint,   \* Predict interval (positive integer)
    Messages        \* Set of possible messages

\* ----------------------------------------------------------------------
\* Assumptions about the constants
ASSUME /\ SendPoint > 0
       /\ PredictPoint > 0
       /\ SendPoint % PredictPoint # 0   \* not a multiple of each other
       /\ PredictPoint % SendPoint # 0
       /\ Messages = { [type |-> "Alive", src |-> p, dst |-> q] : 
                        p \in Proc, q \in Proc \ {p} }

\* ----------------------------------------------------------------------
\* Variables
VARIABLES 
    clock,      \* [p \in Proc -> Nat]   local clock of each process
    last,       \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]   ticks since last heard
    timeout,    \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]   adaptive timeout
    suspect,    \* [p \in Proc -> SUBSET Proc]                suspicion set
    outbox      \* [p \in Proc -> SUBSET Messages]            messages to be sent

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ clock   = [p \in Proc |-> 0]
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
    /\ last    = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
    /\ outbox  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
AliveMessage(p, q) == [type |-> "Alive", src |-> p, dst |-> q]

\* ----------------------------------------------------------------------
\* Actions for a single process p
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMessage(p, q) : q \in Proc \ {p} }]
    /\ clock'  = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last'   = [last EXCEPT ![p][q] = 
                    IF q # p /\ last[p][q] < timeout[p][q] 
                       THEN last[p][q] + 1 
                       ELSE last[p][q] ]
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = 
                    suspect[p] \cup 
                    { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last'    = [last EXCEPT ![p][q] = last[p][q] + 1]
    /\ UNCHANGED <<outbox, timeout>>

Receive(p) ==
    /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \E R \subseteq Proc \ {p} :
         /\ (* R is the set of processes from which p receives an Alive message *)
            suspect' = [suspect EXCEPT ![p] = suspect[p] \ R]
         /\ timeout' = [timeout EXCEPT ![p][q] = 
                         IF q \in R /\ q \in suspect[p] 
                            THEN timeout[p][q] + 1 
                            ELSE timeout[p][q] ]
         /\ last'    = [last EXCEPT ![p][q] = 
                         IF q \in R 
                            THEN 0 
                            ELSE last[p][q] + 1 ]
         /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
         /\ UNCHANGED outbox

\* ----------------------------------------------------------------------
\* Global next-state relation
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Variables tuple used for the stuttering operator
vars == <<clock, last, timeout, suspect, outbox>>

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

Specification == Spec   \* alias with the exact name requested

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ clock   \in [Proc -> Nat]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ outbox  \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : 
         \A q \in Proc \ {p} : 
            timeout[p][q] >= 0 /\ last[p][q] >= 0

\* ----------------------------------------------------------------------
\* (No additional properties are specified)

====