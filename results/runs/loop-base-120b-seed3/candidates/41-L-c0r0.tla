---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Positive integer send interval
    PredictPoint,  \* Positive integer predict interval
    Messages       \* Set of possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    clock,        \* [p \in Proc -> Nat]   local clocks
    timeout,      \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]   adaptive timeouts
    lastHeard,    \* [p \in Proc -> [q \in Proc \ {p} -> Nat]]   ticks since last alive
    suspicion,    \* [p \in Proc -> SUBSET Proc]                current suspicion sets
    outbox        \* [p \in Proc -> SUBSET Messages]           messages to be sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Maximum relevant threshold for a process p (used to wrap the clock)
MaxThresh(p) == 
    LET tSet == { timeout[p][q] : q \in Proc \ {p} } \cup {SendPoint, PredictPoint} 
    IN  IF tSet = {} THEN 0 ELSE Max(tSet)

\* Increment the local clock of p, wrapping to 0 when exceeding MaxThresh(p)
IncClock(p) == 
    LET new == clock[p] + 1 
    IN IF new > MaxThresh(p) THEN 0 ELSE new

\* Increment last‑heard counters for all q \neq p, respecting timeout
IncLastHeard(p) == 
    [q \in Proc \ {p} |-> 
        IF lastHeard[p][q] < timeout[p][q] 
        THEN lastHeard[p][q] + 1 
        ELSE lastHeard[p][q]]

\* Increment last‑heard counters for all q \neq p (unconditional)
IncLastHeardAll(p) == 
    [q \in Proc \ {p} |-> lastHeard[p][q] + 1]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init == 
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
    /\ suspicion = [p \in Proc |-> {}]
    /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK == 
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Process actions
\* ----------------------------------------------------------------------
SendAlive(p) == 
    /\ (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0)
    /\ outbox' = [outbox EXCEPT ![p] = 
          outbox[p] \cup { [sender |-> p, receiver |-> q, type |-> "alive"] : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = IncClock(p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncLastHeard(p)]
    /\ UNCHANGED << timeout, suspicion >>

Predict(p) == 
    /\ (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0)
    /\ suspicion' = [suspicion EXCEPT ![p] = 
          suspicion[p] \cup { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = IncClock(p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = IncLastHeardAll(p)]
    /\ UNCHANGED << timeout, outbox >>

Receive(p) == 
    /\ ~((clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0))
    /\ ~((clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0))
    /\ \E recv \subseteq { m \in Messages : 
            /\ m.receiver = p 
            /\ m.type = "alive" } :
        LET senders == { m.sender : m \in recv } IN
        /\ clock' = [clock EXCEPT ![p] = IncClock(p)]
        /\ lastHeard' = [lastHeard EXCEPT ![p] = 
              [q \in Proc \ {p} |-> 
                  IF q \in senders THEN 0 ELSE lastHeard[p][q] + 1]]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ senders]
        /\ timeout' = [timeout EXCEPT ![p] = 
              [q \in Proc \ {p} |-> 
                  IF q \in senders /\ q \in suspicion[p] 
                  THEN timeout[p][q] + 1 
                  ELSE timeout[p][q]]]
        /\ outbox' = outbox

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
vars == <<clock, timeout, lastHeard, suspicion, outbox>>

SPECIFICATION == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Required identifiers (aliases for the configuration file)
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANTS == TypeOK
PROPERTIES == TRUE

====