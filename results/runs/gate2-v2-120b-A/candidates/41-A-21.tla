---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (set in the .cfg)
\* ----------------------------------------------------------------------
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,  \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages       \* Set of possible alive messages (defined below)

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"Alive"}, src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,    \* [p \in Proc |-> SUBSET Proc]   -- processes p suspects
    timeout,      \* [p \in Proc |-> [q \in Proc |-> Nat]] -- adaptive timeouts
    lastHeard,    \* [p \in Proc |-> [q \in Proc |-> Nat]] -- ticks since last alive from q
    clock,        \* [p \in Proc |-> Nat]                -- local clock
    outbox        \* [p \in Proc |-> SUBSET Message]     -- messages to be sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllProcessesExcept(p) == Proc \ {p}

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Process actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0            \* ensure not simultaneous
    /\ outbox' = [outbox EXCEPT ![p] = 
          outbox[p] \cup { [type |-> "Alive", src |-> p, dst |-> q] : q \in AllProcessesExcept(p) }]
    /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
          IF q \in AllProcessesExcept(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] 
          : q \in Proc]
    /\ UNCHANGED <<suspicion, timeout, outbox>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0               \* ensure not simultaneous
    /\ let newSus == { q \in AllProcessesExcept(p) :
            lastHeard[p][q] > timeout[p][q] } IN
       /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
          IF q \in AllProcessesExcept(p) THEN lastHeard[p][q] + 1 ELSE lastHeard[p][q] 
          : q \in Proc]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ \E msg \in outbox[p] : msg.type = "Alive" \* there is at least one incoming alive
    /\ LET srcs == { msg.src : msg \in outbox[p] } IN
       /\ suspicion' = [suspicion EXCEPT ![p] = 
            suspicion[p] \ { src : src \in srcs }]
    /\ timeout' = [timeout EXCEPT ![p][src] = 
            IF src \in suspicion[p] THEN timeout[p][src] + 1 ELSE timeout[p][src] 
            : src \in srcs]
    /\ lastHeard' = [lastHeard EXCEPT ![p][src] = 0 : src \in srcs]
    /\ clock' = [clock EXCEPT ![p] = 0]      \* clock reset after processing
    /\ outbox' = [outbox EXCEPT ![p] = {}]   \* clear processed messages
    /\ UNCHANGED <<suspicion, timeout>>

Idle(p) ==
    /\ /\ clock[p] % SendPoint # 0
       /\ clock[p] % PredictPoint # 0
    /\ UNCHANGED <<suspicion, timeout, lastHeard, clock, outbox>>

ProcessStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ Idle(p)

Next ==
    \E p \in Proc : ProcessStep(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant (the only required invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
Init == Init
Next == Next
TypeOK == TypeOK

====