---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* Helper definitions
IsMultiple(v, i) == v \in i * Nat

AliveMessage(p, q) == [type |-> "alive", src |-> p, dst |-> q]

MaxClock == 
    LET timeoutVals == { timeout[p][q] : p \in Proc, q \in Proc } IN
    Max({SendPoint, PredictPoint} \cup timeoutVals)

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    suspect,   \* [p \in Proc -> SUBSET Proc]   suspicion set of each process
    timeout,   \* [p \in Proc -> [q \in Proc -> Nat]]   timeout intervals
    last,      \* [p \in Proc -> [q \in Proc -> Nat]]   last‑heard counters
    clock,     \* [p \in Proc -> Nat]   local clocks
    outbox     \* [p \in Proc -> SUBSET Messages]   messages to be sent

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock   = [p \in Proc |-> 0]
    /\ outbox  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions for a single process p
SendAlive(p) ==
    /\ IsMultiple(clock[p], SendPoint) /\ ~IsMultiple(clock[p], PredictPoint)
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMessage(p, q) : q \in Proc \ {p} }]
    /\ clock'  = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last'   = [last EXCEPT ![p][q] = 
                    IF q # p /\ last[p][q] < timeout[p][q] 
                    THEN last[p][q] + 1 
                    ELSE last[p][q] ]
    /\ suspect' = suspect
    /\ timeout' = timeout
    /\ UNCHANGED << suspect, timeout, last, clock, outbox >> \* other components unchanged

Predict(p) ==
    /\ IsMultiple(clock[p], PredictPoint) /\ ~IsMultiple(clock[p], SendPoint)
    /\ suspect' = [suspect EXCEPT ![p] = 
                    suspect[p] \cup 
                    { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ clock'  = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last'   = [last EXCEPT ![p][q] = last[p][q] + 1]
    /\ outbox' = outbox
    /\ timeout' = timeout
    /\ UNCHANGED << suspect, timeout, last, clock, outbox >>

Receive(p) ==
    /\ ~IsMultiple(clock[p], SendPoint) /\ ~IsMultiple(clock[p], PredictPoint)
    /\ \E rec \in SUBSET { m \in Messages : 
                            /\ m.type = "alive"
                            /\ m.dst = p } :
        LET srcs == { m.src : m \in rec } IN
        /\ last'   = [last EXCEPT ![p][q] = 
                        IF q \in srcs 
                        THEN 0 
                        ELSE last[p][q] + 1]
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ srcs]
        /\ timeout' = [timeout EXCEPT ![p][q] = 
                        IF q \in srcs /\ q \in suspect[p] 
                        THEN timeout[p][q] + 1 
                        ELSE timeout[p][q]]
        /\ clock'   = [clock EXCEPT ![p] = 
                        IF clock[p] + 1 > MaxClock 
                        THEN 0 
                        ELSE clock[p] + 1]
        /\ outbox'  = [outbox EXCEPT ![p] = {}]
        /\ UNCHANGED << suspect, timeout, last, clock, outbox >>

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving of process actions)
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<suspect, timeout, last, clock, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ clock   \in [Proc -> Nat]
    /\ outbox  \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* The required identifiers for the configuration
\*   CONSTANTS: Proc, d0, SendPoint, PredictPoint, Messages
\*   INIT predicate: Init
\*   INVARIANTS: TypeOK

====