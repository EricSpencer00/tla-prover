---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible alive messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc] set of processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] timeout interval p uses for q
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] ticks since p last heard from q
    clock,       \* [p \in Proc |-> Nat] local clock of each process
    outMsgs,     \* [p \in Proc |-> SUBSET Messages] messages p intends to send this step
    inMsgs       \* [p \in Proc |-> SUBSET Messages] messages p receives this step

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ProcSet == Proc

ProcPairs == { <<p, q>> : p \in ProcSet /\ q \in ProcSet }

IsAlive(m) == 
    \E p, q \in ProcSet : m = << "Alive", p, q >>

Sender(m) == 
    IF \E p, q \in ProcSet : m = << "Alive", p, q >> THEN p ELSE ""

Receiver(m) == 
    IF \E p, q \in ProcSet : m = << "Alive", p, q >> THEN q ELSE ""

Init ==
    /\ suspicion = [p \in ProcSet |-> {}]
    /\ timeout   = [p \in ProcSet |-> [q \in ProcSet |-> d0]]
    /\ lastHeard = [p \in ProcSet |-> [q \in ProcSet |-> 0]]
    /\ clock     = [p \in ProcSet |-> 0]
    /\ outMsgs   = [p \in ProcSet |-> {}]
    /\ inMsgs    = [p \in ProcSet |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0               \* not a predict step
    /\ outMsgs' = [outMsgs EXCEPT ![p] = { << "Alive", p, q >> : q \in ProcSet }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                         IF q \in suspicion[p] 
                         THEN lastHeard[p][q] 
                         ELSE lastHeard[p][q] + 1
                     \* note: counters for suspected processes do not advance
                     ]
    /\ UNCHANGED <<suspicion, timeout, inMsgs>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0                  \* not a send step
    /\ \E q \in ProcSet :
          (lastHeard[p][q] >= timeout[p][q]) /\ q # p
    /\ suspicion' = [suspicion EXCEPT 
                        ![p] = suspicion[p] \cup 
                               { q \in ProcSet : q # p /\ lastHeard[p][q] >= timeout[p][q] }]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1]
    /\ clock'     = [clock EXCEPT ![p] = clock[p] + 1]
    /\ UNCHANGED <<timeout, outMsgs, inMsgs>>

Receive(p) ==
    /\ \A m \in inMsgs[p] : IsAlive(m)
    /\ \A m \in inMsgs[p] : Sender(m) # p
    /\ outMsgs' = [outMsgs EXCEPT ![p] = {}]
    /\ clock'   = [clock EXCEPT ![p] = 
                      IF clock[p] + 1 > Max({SendPoint, PredictPoint} 
                                            \cup { timeout[p][q] : q \in ProcSet })
                      THEN 0
                      ELSE clock[p] + 1]
    /\ lastHeard' = 
        [lastHeard EXCEPT 
            ![p][q] = 
                IF q \in { Receiver(m) : m \in inMsgs[p] } 
                THEN 0 
                ELSE lastHeard[p][q] + 1]
    /\ suspicion' = 
        [suspicion EXCEPT 
            ![p] = suspicion[p] \ 
                  { q \in ProcSet : q \in { Receiver(m) : m \in inMsgs[p] } }]
    /\ timeout' = 
        [timeout EXCEPT 
            ![p][q] = 
                IF q \in { Receiver(m) : m \in inMsgs[p] } /\ q \in suspicion[p] 
                THEN timeout[p][q] + 1 
                ELSE timeout[p][q]]
    /\ UNCHANGED inMsgs

Step(p) == 
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)

Next ==
    \E p \in ProcSet : Step(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outMsgs, inMsgs>>

\* ----------------------------------------------------------------------
\* Type invariant (as required)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outMsgs   \in [Proc -> SUBSET Messages]
    /\ inMsgs    \in [Proc -> SUBSET Messages]

=============================================================================