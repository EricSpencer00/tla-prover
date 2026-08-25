---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Proc,           \* Set of process identifiers
    d0,             \* Default timeout interval (positive integer)
    SendPoint,      \* Positive integer: send interval
    PredictPoint,   \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages        \* Set of all possible messages

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsMultiple(n, k) == 
    /\ k # 0
    /\ \E m \in Nat : n = k * m

AliveMsg(p, q) == [src |-> p, dst |-> q, type |-> "alive"]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    clock,          \* [p \in Proc -> Nat]  local logical clock of each process
    suspicion,      \* [p \in Proc -> SUBSET Proc]  set of processes p suspects
    timeout,        \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]  adaptive timeout intervals
    lastHeard,      \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]  ticks since p last heard from q
    outbox          \* [p \in Proc -> SUBSET Messages]  messages p wants to send

vars == <<clock, suspicion, timeout, lastHeard, outbox>>

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
    /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Action: Send alive messages
\* ----------------------------------------------------------------------
Send(p) ==
    /\ IsMultiple(clock[p], SendPoint)
    /\ ~IsMultiple(clock[p], PredictPoint)   \* send and predict never coincide
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMsg(p, q) : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
           ![p] = [ q \in Proc \ {p} |-> 
                    IF lastHeard[p][q] < timeout[p][q] 
                    THEN lastHeard[p][q] + 1 
                    ELSE lastHeard[p][q] ] ]
    /\ UNCHANGED <<suspicion, timeout>>

\* ----------------------------------------------------------------------
\* Action: Make predictions (update suspicion set)
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ IsMultiple(clock[p], PredictPoint)
    /\ ~IsMultiple(clock[p], SendPoint)
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT 
           ![p] = [ q \in Proc \ {p} |-> lastHeard[p][q] + 1 ]]
    /\ suspicion' = [suspicion EXCEPT 
           ![p] = suspicion[p] \cup 
                 { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } ]
    /\ UNCHANGED <<outbox, timeout>>

\* ----------------------------------------------------------------------
\* Action: Receive incoming messages (any subset may be delivered)
\* ----------------------------------------------------------------------
Receive(p) ==
    LET inc == SUBSET { m \in Messages : m.dst = p } IN
    /\ inc \subseteq { m \in Messages : m.dst = p }
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ outbox' = outbox
    /\ lastHeard' = [lastHeard EXCEPT 
           ![p] = [ q \in Proc \ {p} |-> 
                    IF \E m \in inc : m.src = q /\ m.type = "alive"
                    THEN 0
                    ELSE lastHeard[p][q] + 1 ] ]
    /\ suspicion' = [suspicion EXCEPT 
           ![p] = suspicion[p] \ 
                 { q \in Proc \ {p} : \E m \in inc : m.src = q /\ m.type = "alive" } ]
    /\ timeout' = [timeout EXCEPT 
           ![p] = [ q \in Proc \ {p} |-> 
                    IF q \in suspicion[p] /\ \E m \in inc : m.src = q /\ m.type = "alive"
                    THEN timeout[p][q] + 1
                    ELSE timeout[p][q] ] ]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : 
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant (safety)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc \ {Proc} -> Nat]]
    /\ lastHeard \in [Proc -> [Proc \ {Proc} -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification (for completeness)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Properties (the config may refer to this name)
\* ----------------------------------------------------------------------
Properties == TypeOK

====