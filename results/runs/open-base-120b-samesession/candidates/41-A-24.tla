---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer, send interval
    PredictPoint,  \* Positive integer, predict interval (not a multiple of SendPoint)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    clock,        \* [p \in Proc |-> Nat] : local clock of each process
    suspicion,    \* [p \in Proc |-> SUBSET Proc] : processes suspected by p
    timeout,      \* [p \in Proc |-> [q \in Proc \ {p} |-> Nat]] : adaptive timeout values
    lastHeard,    \* [p \in Proc |-> [q \in Proc \ {p} |-> Nat]] : ticks since last alive from q
    outbox        \* [p \in Proc |-> SUBSET Messages] : messages p intends to send

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
IsSend(p) == 
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0

IsPredict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Send(p) == 
    /\ IsSend(p)
    /\ outbox' = [outbox EXCEPT ![p] = 
            { [type |-> "alive", from |-> p, to |-> q] : q \in Proc \ {p} } ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
            IF q # p THEN lastHeard[p][q] + 1 ELSE @]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) == 
    /\ IsPredict(p)
    /\ LET newSus \in SUBSET (Proc \ {p}) == 
            { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }
       IN
          suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1 
                     \* increment all counters (including those just added to suspicion) 
                     \* (the increment for a newly timed‑out process does not affect correctness) 
                     \* because it will be superseded by the next receive if a message arrives. 
                     \* 
                     ]
    /\ UNCHANGED <<outbox, timeout>>

Receive(p) == 
    /\ ~IsSend(p) /\ ~IsPredict(p)
    /\ \E recSet \in SUBSET (Proc \ {p}) :
        /\ lastHeard' = [lastHeard EXCEPT ![p][q] = 
                IF q \in recSet THEN 0 ELSE lastHeard[p][q] + 1]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ recSet]
        /\ timeout' = [timeout EXCEPT ![p][q] = 
                IF q \in recSet /\ q \in suspicion[p] 
                THEN timeout[p][q] + 1 
                ELSE timeout[p][q]]
        /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
        /\ outbox' = outbox
        /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next == 
    \E p \in Proc : \/ Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
    /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_<<clock, suspicion, timeout, lastHeard, outbox>>

\* ----------------------------------------------------------------------
\* Property placeholder (no liveness properties required)
\* ----------------------------------------------------------------------
PROPERTIES == TypeOK

====