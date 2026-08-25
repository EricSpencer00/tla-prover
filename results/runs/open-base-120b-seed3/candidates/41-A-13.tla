---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Set of clock values at which a process sends alive messages
    PredictPoint,  \* Set of clock values at which a process makes predictions
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc -> SUBSET Proc]  : processes p suspects
    timeout,     \* [p \in Proc -> [q \in Proc -> Nat]] : adaptive timeout intervals
    lastHeard,   \* [p \in Proc -> [q \in Proc -> Nat]] : ticks since p last heard from q
    clock,       \* [p \in Proc -> Nat]                : local clock of each process
    channel      \* SUBSET Messages                     : messages in transit

\* ----------------------------------------------------------------------
\* Derived sets and helper definitions
\* ----------------------------------------------------------------------
\* The set of all possible alive messages (used only for readability;
\* the actual set is given by the constant *Messages* in the configuration)
AliveMessage(p, q) == 
    [type |-> "alive", from |-> p, to |-> q]

AllAliveMessages(p) == { AliveMessage(p, q) : q \in Proc \ {p} }

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ channel   \in SUBSET Messages

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF p = q THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ channel   = {}

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ p \in Proc
    /\ clock[p] \in SendPoint
    /\ clock[p] \notin PredictPoint
    /\ channel' = channel \cup AllAliveMessages(p)
    /\ clock'   = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p][q] = IF q # p /\ @ < timeout[p][q] THEN @ + 1 ELSE @
                     ]
    /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
    /\ p \in Proc
    /\ clock[p] \in PredictPoint
    /\ clock[p] \notin SendPoint
    /\ LET newSus == { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } IN
        suspicion' = [suspicion EXCEPT ![p] = @ \cup newSus]
    /\ clock'     = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p][q] = @ + 1
                     ]
    /\ UNCHANGED << timeout, channel >>

Receive(p) ==
    /\ p \in Proc
    /\ clock[p] \notin SendPoint
    /\ clock[p] \notin PredictPoint
    /\ LET recv == { m \in channel : m.to = p } IN
       /\ channel' = channel \ setdiff recv
       /\ clock'   = [clock EXCEPT ![p] = @ + 1]
       /\ \* Update lastHeard, suspicion and (optionally) timeout for each
          \* received alive message
          /\ \A m \in recv :
                /\ lastHeard' = [lastHeard EXCEPT ![p][m.from] = 0]
                /\ suspicion' = [suspicion EXCEPT ![p] = @ \ setminus {m.from}]
                /\ timeout'   = [timeout EXCEPT 
                                   ![p][m.from] = IF m.from \in @ THEN @ + 1 ELSE @]
       /\ UNCHANGED << suspicion, timeout >> \* (the above overrides for each m)
    /\ UNCHANGED << suspicion, timeout >> \* redundant but keeps model simple

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << suspicion, timeout, lastHeard, clock, channel >>

Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Required identifiers for the configuration file
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANTS == << TypeOK >>
PROPERTIES == << >>          \* no additional temporal properties specified
SPECIFICATION == Spec

====