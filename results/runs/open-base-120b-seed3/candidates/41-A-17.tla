---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

\*-----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the .cfg file)
\*-----------------------------------------------------------------------
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (Nat)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of possible messages (e.g., alive messages)

\*-----------------------------------------------------------------------
\* VARIABLES
\*-----------------------------------------------------------------------
VARIABLES
    suspicion,     \* [p \in Proc |-> SUBSET Proc]   -- suspected processes per process
    timeout,       \* [p \in Proc |-> [q \in Proc |-> Nat]]   -- adaptive timeout per pair
    lastHeard,     \* [p \in Proc |-> [q \in Proc |-> Nat]]   -- ticks since last alive from q
    clock,         \* [p \in Proc |-> Nat]       -- local clock per process
    outbox         \* [p \in Proc |-> SUBSET Messages]  -- messages to be sent

\*-----------------------------------------------------------------------
\* Helper definitions
\*-----------------------------------------------------------------------
\* The set of all other processes (excluding self)
Other(p) == Proc \ {p}

\* Record representing an alive message from p to q
AliveMsg(p,q) == [type |-> "Alive", src |-> p, dst |-> q]

\*-----------------------------------------------------------------------
\* Initial state
\*-----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\*-----------------------------------------------------------------------
\* Actions for a single process p
\*-----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox'   = [outbox EXCEPT ![p] = outbox[p] \cup { AliveMsg(p,q) : q \in Other(p) }]
    /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
                       [lastHeard[p] EXCEPT ![q] = lastHeard[p][q] + 1 
                                            \* for all q \in Proc 
                       ]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = 
                       suspicion[p] \cup
                       { q \in Other(p) : lastHeard[p][q] > timeout[p][q] } ]
    /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
                       [lastHeard[p] EXCEPT ![q] = lastHeard[p][q] + 1 
                                            \* for all q \in Proc 
                       ]]
    /\ UNCHANGED <<timeout, outbox>>

\* Receive action: nondeterministically receive a set S of alive messages
Receive(p) ==
    /\ \E S \subseteq Other(p) :
          /\ (* we imagine that an alive message from each q \in S is received *)
          /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ S]
          /\ lastHeard' = [lastHeard EXCEPT ![p] = 
                             [lastHeard[p] EXCEPT 
                                ![q] = IF q \in S THEN 0 ELSE lastHeard[p][q] + 1]]
          /\ timeout'   = [timeout EXCEPT ![p] = 
                             [timeout[p] EXCEPT 
                                ![q] = IF q \in S /\ q \in suspicion[p] 
                                      THEN timeout[p][q] + 1 
                                      ELSE timeout[p][q]]]
          /\ UNCHANGED <<clock, outbox>>

\*-----------------------------------------------------------------------
\* Overall Next action: choose a process and let it perform exactly one
\* of the three possible actions.
\*-----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\*-----------------------------------------------------------------------
\* State vector for the temporal operators
\*-----------------------------------------------------------------------
vars == <<suspicion, timeout, lastHeard, clock, outbox>>

\*-----------------------------------------------------------------------
\* Specification
\*-----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars

SPECIFICATION == Spec

\*-----------------------------------------------------------------------
\* Type invariant
\*-----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

INVARIANTS == TypeOK

\*-----------------------------------------------------------------------
\* (No additional properties are required)
\*-----------------------------------------------------------------------
PROPERTIES == TRUE

====