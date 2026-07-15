---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value
    SendPoint,     \* Positive integer send interval
    PredictPoint,  \* Positive integer predict interval
    Messages       \* Set of possible message records

\* ----------------------------------------------------------------------
\* Message definition
Message == [src : Proc, dst : Proc, type : {"Alive"}]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    suspicion,   \* [p \in Proc |-> Subset of Proc] : processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] : adaptive timeouts
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] : ticks since last alive from q
    clock,       \* [p \in Proc |-> Nat] : local clock of each process
    outbox,      \* [p \in Proc |-> SUBSET Message] : messages ready to send
    inbox        \* [p \in Proc |-> SUBSET Message] : messages received this step

\* ----------------------------------------------------------------------
\* Helper definitions
AllExcept(p) == { q \in Proc : q # p }

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]
    /\ inbox     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* SendAlive action for a single process p
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { [src |-> p, dst |-> q, type |-> "Alive"]
                                          : q \in AllExcept(p) }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p][q] = IF lastHeard[p][q] >= timeout[p][q] THEN timeout[p][q]
                                  ELSE lastHeard[p][q] + 1
                        : q \in AllExcept(p)]
    /\ UNCHANGED <<suspicion, timeout, inbox>>

\* ----------------------------------------------------------------------
\* Predict action for a single process p
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT
                        ![p] = suspicion[p] \cup
                               { q \in AllExcept(p) :
                                   lastHeard[p][q] > timeout[p][q] }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p][q] = IF lastHeard[p][q] >= timeout[p][q] THEN timeout[p][q]
                                  ELSE lastHeard[p][q] + 1
                        : q \in AllExcept(p)]
    /\ UNCHANGED <<outbox, timeout, inbox>>

\* ----------------------------------------------------------------------
\* Receive action for a single process p
Receive(p) ==
    /\ \A m \in inbox[p] :
          /\ m.type = "Alive"
          /\ m.dst = p
    /\ \A m \in outbox[p] : m.type = "Alive"
    /\ \A m \in outbox[p] : m.dst \in AllExcept(p)
    /\ \A m \in inbox[p] : m.src \in AllExcept(p)
    /\ \A p \in Proc : \E m \in inbox[p] : m.type = "Alive"
    /\ \E src \in AllExcept(p) :
         /\ [src |-> src, dst |-> p, type |-> "Alive"] \in inbox[p]
    /\ suspicion' = [suspicion EXCEPT ![p][src] = {}]
    /\ lastHeard' = [lastHeard EXCEPT ![p][src] = 0]
    /\ timeout' = IF src \in suspicion[p]
                     THEN [timeout EXCEPT ![p][src] = timeout[p][src] + 1]
                     ELSE timeout
    /\ clock' = [clock EXCEPT ![p] = IF clock[p] + 1 > Max(SendPoint, PredictPoint, 
                                                          MAX_{q \in AllExcept(p)} timeout[p][q])
                                 THEN 0
                                 ELSE clock[p] + 1]
    /\ outbox' = [outbox EXCEPT ![p] = {}]
    /\ inbox'  = [inbox  EXCEPT ![p] = {}]
    /\ UNCHANGED <<suspicion, timeout, lastHeard>>

\* ----------------------------------------------------------------------
\* Stuttering (no-op) action, needed for weak fairness
Stutter ==
    UNCHANGED <<suspicion, timeout, lastHeard, clock, outbox, inbox>>

\* ----------------------------------------------------------------------
\* Next-state relation: choose a process and perform one of its actions
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)
        \/ Stutter

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox, inbox>>

\* ----------------------------------------------------------------------
\* Type correctness invariant
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Message]
    /\ inbox     \in [Proc -> SUBSET Message]
    /\ \A p \in Proc :
        /\ \A m \in outbox[p] :
               /\ m.type = "Alive"
               /\ m.src = p
               /\ m.dst \in AllExcept(p)
        /\ \A m \in inbox[p] :
               /\ m.type = "Alive"
               /\ m.dst = p
               /\ m.src \in AllExcept(p)

\* ----------------------------------------------------------------------
\* The only property asked for in the .cfg file
THEOREM Spec => []TypeOK

====