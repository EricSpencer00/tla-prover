---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer, not multiple of SendPoint)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    clock,        \* [p \in Proc -> Nat]   local clock of each process
    suspicion,    \* [p \in Proc -> SUBSET Proc]   processes p suspects
    timeout,      \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]  adaptive timeout intervals
    lastHeard,    \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]  ticks since last alive from q
    outbox        \* [p \in Proc -> SUBSET Messages]  messages p wants to send

\* ----------------------------------------------------------------------
\* Helper definitions
AliveMsg(p,q) == 
    [type |-> "alive", from |-> p, to |-> q]

\* Increment last-heard counters for a process p on all q that have not timed‑out
IncLastHeard(p, ls, to) ==
    [q \in DOMAIN ls[p] |-> 
        IF ls[p][q] < to[p][q] 
        THEN ls[p][q] + 1 
        ELSE ls[p][q]]

\* Reset last‑heard counter for (p,q) to 0
ResetLastHeard(p, q, ls) ==
    [ls EXCEPT ![p][q] = 0]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
    /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions for a single process p
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = 
            { m \in Messages : 
                /\ m.type = "alive"
                /\ m.from = p
                /\ m.to \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncLastHeard(p, lastHeard, timeout)]
    /\ suspicion' = suspicion
    /\ timeout' = timeout

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = 
            [q \in DOMAIN lastHeard[p] |-> lastHeard[p][q] + 1]]
    /\ suspicion' = [suspicion EXCEPT ![p] = 
            suspicion[p] \cup
            { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ outbox' = outbox
    /\ timeout' = timeout

Receive(p) ==
    /\ \* This action fires when neither send nor predict condition holds
       ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0) 
    /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \* Collect all alive messages addressed to p
       let msgs == { m \in UNION { outbox[q] : q \in Proc } :
                       /\ m.type = "alive"
                       /\ m.to = p } in
       /\ \* Update lastHeard, suspicion and timeout for each sender
          \E senderSet == { m.from : m \in msgs } :
              /\ lastHeard' = [lastHeard EXCEPT 
                     ![p][q] = IF q \in senderSet THEN 0 ELSE @ 
                     FOR q \in Proc \ {p}]
              /\ suspicion' = [suspicion EXCEPT 
                     ![p] = suspicion[p] \ { q \in senderSet }]
              /\ timeout' = [timeout EXCEPT 
                     ![p][q] = IF q \in senderSet /\ q \in suspicion[p] 
                                 THEN @ + 1 
                                 ELSE @ 
                     FOR q \in Proc \ {p}]]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ outbox' = [outbox EXCEPT ![q] = {} FOR q \in Proc]

\* ----------------------------------------------------------------------
\* Next-state relation: one process takes one of its actions
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    Init /\ [][Next]_<<clock, suspicion, timeout, lastHeard, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc \ {#} -> Nat]]
    /\ lastHeard \in [Proc -> [Proc \ {#} -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc :
        \A q \in Proc \ {p} :
            /\ timeout[p][q] >= 0
            /\ lastHeard[p][q] >= 0

\* ----------------------------------------------------------------------
\* Required identifiers for the .cfg file
INIT == Init
NEXT == Next
INVARIANTS == TypeOK
SPECIFICATION == Spec
PROPERTIES == {}

============================================================================