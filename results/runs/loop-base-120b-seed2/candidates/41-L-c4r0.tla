---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS 
    Proc,        \* The set of process identifiers
    d0,          \* Default timeout value (positive integer)
    SendPoint,   \* Period for sending alive messages (positive integer)
    PredictPoint,\* Period for making predictions (positive integer)
    Messages     \* Set of possible messages

\* ----------------------------------------------------------------------
\* Message definition (alive messages only)
Message == [type : {"Alive"}, src : Proc, dst : Proc]

ASSUME Messages \subseteq Message

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    clock,      \* [p \in Proc |-> Nat]  local clock of each process
    suspicion,  \* [p \in Proc |-> SUBSET Proc]  set of processes suspected by p
    timeout,    \* [p \in Proc |-> [q \in Proc |-> Nat]]  adaptive timeout intervals
    last,       \* [p \in Proc |-> [q \in Proc |-> Nat]]  ticks since last heard
    out         \* [p \in Proc |-> SUBSET Messages]  messages p intends to send

\* ----------------------------------------------------------------------
\* Derived constant for clock wrap‑around
MaxClock == SendPoint * PredictPoint

\* ----------------------------------------------------------------------
\* Type invariant (required identifier)
TypeOK == 
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ out \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : suspicion[p] \subseteq Proc \ {p}
    /\ \A p \in Proc : \A q \in Proc \ {p} :
          out[p] = {} \/ 
          (\A m \in out[p] : 
               /\ m.type = "Alive"
               /\ m.src = p
               /\ m.dst \in Proc \ {p})

\* ----------------------------------------------------------------------
\* Initial state (required identifier: Init)
Init == 
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ out = [p \in Proc |-> {}]
    /\ SendPoint > 0
    /\ PredictPoint > 0
    /\ SendPoint # PredictPoint

\* ----------------------------------------------------------------------
\* Helper: increment all last‑heard counters of p (except to itself)
IncLast(p) == 
    [last EXCEPT ![p] = 
        [last[p] EXCEPT ![q] = 
            IF q # p THEN last[p][q] + 1 ELSE @
            \FORALL q \in Proc]]

\* ----------------------------------------------------------------------
\* Action: Send alive messages
SendAlive(p) == 
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = 
                { [type |-> "Alive", src |-> p, dst |-> q] : q \in Proc \ {p} } ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last' = IncLast(p)
    /\ UNCHANGED <<suspicion, timeout>>

\* ----------------------------------------------------------------------
\* Action: Make predictions (suspend processes)
Predict(p) == 
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = 
                      suspicion[p] \cup 
                      { q \in Proc \ {p} : last[p][q] > timeout[p][q] } ]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last' = IncLast(p)
    /\ UNCHANGED <<out, timeout>>

\* ----------------------------------------------------------------------
\* Action: Receive (or idle) step
Receive(p) == 
    /\ clock[p] % SendPoint # 0
    /\ clock[p] % PredictPoint # 0
    /\ \E R \in SUBSET (Proc \ {p}) :
          LET newLast == 
                [last[p] EXCEPT ![q] = IF q \in R THEN 0 ELSE last[p][q] + 1] 
          IN
          LET newSusp == suspicion[p] \ R 
          IN
          LET newTO == 
                [timeout[p] EXCEPT ![q] = 
                    IF q \in R /\ q \in suspicion[p] 
                    THEN timeout[p][q] + 1 
                    ELSE timeout[p][q] 
                    \FORALL q \in Proc] 
          IN
          /\ last' = [last EXCEPT ![p] = newLast]
          /\ suspicion' = [suspicion EXCEPT ![p] = newSusp]
          /\ timeout' = [timeout EXCEPT ![p] = newTO]
          /\ clock' = [clock EXCEPT ![p] = 
                        IF clock[p] + 1 > MaxClock THEN 0 ELSE clock[p] + 1]
          /\ out' = out

\* ----------------------------------------------------------------------
\* Next-state relation (required identifier)
Next == 
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification (required identifier)
SPECIFICATION == Init /\ [][Next]_<<clock, suspicion, timeout, last, out>>

\* ----------------------------------------------------------------------
\* Invariants list (required identifier)
INVARIANTS == TypeOK

\* ----------------------------------------------------------------------
\* Additional properties placeholder (required identifier)
PROPERTIES == TRUE

====