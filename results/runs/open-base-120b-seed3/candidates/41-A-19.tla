---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS
    Proc,          \* The set of processes
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Positive send interval (integer)
    PredictPoint,  \* Positive predict interval (integer)
    Messages       \* The set of possible messages

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Message == [type : {"alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    suspects,   \* [p \in Proc |-> SUBSET Proc]  (process p's suspicion set)
    timeout,    \* [p \in Proc |-> [q \in Proc |-> Nat]] (adaptive timeout intervals)
    lastHeard,  \* [p \in Proc |-> [q \in Proc |-> Nat]] (ticks since last message)
    clock,      \* [p \in Proc |-> Nat] (local clock)
    outgoing    \* [p \in Proc |-> SUBSET Messages] (messages to be sent this step)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsMultiple(v, i) == v % i = 0

MaxTimeout(p) == 
    LET vals == { timeout[p][q] : q \in Proc } IN
        IF vals = {} THEN 0 ELSE Max(vals)

ClockReset(p, newVal) ==
    IF newVal > Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })
        THEN 0
        ELSE newVal

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ suspects = [p \in Proc |-> {}]
    /\ timeout  = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock    = [p \in Proc |-> 0]
    /\ outgoing = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ p \in Proc
    /\ IsMultiple(clock[p], SendPoint)
    /\ ~IsMultiple(clock[p], PredictPoint)          \* send and predict never coincide
    /\ \* create alive messages for all other processes
       outgoing' = [outgoing EXCEPT ![p] = 
                       { [type |-> "alive", from |-> p, to |-> q] :
                           q \in Proc \ {p} } ]
    /\ \* increment counters for processes not yet timed‑out
       lastHeard' = [lastHeard EXCEPT ![p][q] =
                       IF q # p /\ lastHeard[p][q] < timeout[p][q]
                          THEN lastHeard[p][q] + 1
                          ELSE lastHeard[p][q] ]
    /\ \* advance and possibly wrap the clock
       clock' = [clock EXCEPT ![p] = 
                   ClockReset(p, clock[p] + 1)]
    /\ UNCHANGED <<suspects, timeout>>

Predict(p) ==
    /\ p \in Proc
    /\ IsMultiple(clock[p], PredictPoint)
    /\ ~IsMultiple(clock[p], SendPoint)
    /\ \* add newly timed‑out processes to the suspicion set
       suspects' = [suspects EXCEPT ![p] = 
                      suspects[p] \cup
                      { q \in Proc \ {p} :
                          lastHeard[p][q] > timeout[p][q] } ]
    /\ \* increment all counters (including those already timed‑out)
       lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
    /\ \* advance and possibly wrap the clock
       clock' = [clock EXCEPT ![p] = 
                   ClockReset(p, clock[p] + 1)]
    /\ UNCHANGED <<outgoing, timeout>>

Receive(p) ==
    /\ p \in Proc
    /\ ~IsMultiple(clock[p], SendPoint)
    /\ ~IsMultiple(clock[p], PredictPoint)
    /\ \* nondeterministically choose the set of alive messages addressed to p
       \* (the environment provides this set)
       \E rec \subseteq { m \in Messages :
                            /\ m.type = "alive"
                            /\ m.to   = p } :
          /\ \* apply effects of each received message
             LET updLast ==
                 [lastHeard EXCEPT ![p][q] = 
                     IF q \in { m.from : m \in rec } THEN 0
                     ELSE lastHeard[p][q] ]
                 IN
             LET updSus ==
                 [suspects EXCEPT ![p] = 
                     suspects[p] \ { q \in Proc :
                         q \in { m.from : m \in rec } } ]
                 IN
             LET updTimeout ==
                 [timeout EXCEPT ![p][q] = 
                     IF q \in { m.from : m \in rec } /\ q \in suspects[p]
                         THEN timeout[p][q] + 1
                         ELSE timeout[p][q] ]
                 IN
                 /\ lastHeard' = updLast
                 /\ suspects'  = updSus
                 /\ timeout'   = updTimeout
          /\ \* clock advances and may wrap
             clock' = [clock EXCEPT ![p] = 
                         ClockReset(p, clock[p] + 1)]
          /\ UNCHANGED outgoing)

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspects, timeout, lastHeard, clock, outgoing>>

\* ----------------------------------------------------------------------
\* Invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspects \in [Proc -> SUBSET Proc]
    /\ timeout  \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock    \in [Proc -> Nat]
    /\ outgoing \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* The identifiers required by the configuration file
\* ----------------------------------------------------------------------
VARIABLES Init, Next, TypeOK

====