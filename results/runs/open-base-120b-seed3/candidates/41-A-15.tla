---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible messages (provided by the environment)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   – processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] – adaptive timeout intervals
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] – ticks since last alive from q
    clk,         \* [p \in Proc |-> Nat]                – local clock of each process
    outbox       \* [p \in Proc |-> SUBSET Messages]    – messages p wants to send

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Maximum timeout a process p currently uses (excluding itself)
MaxTimeout(p) == 
    LET vals == { timeout[p][q] : q \in Proc \ {p} } IN
    IF vals = {} THEN 0 ELSE Max(vals)

\* Compute the new clock value after one tick, wrapping to 0 when it exceeds
\* all relevant thresholds.
NewClk(p) ==
    LET limit == Max({SendPoint, PredictPoint, MaxTimeout(p)}) IN
    IF clk[p] + 1 > limit THEN 0 ELSE clk[p] + 1

\* Predicate indicating that p should perform a Send action
IsSend(p) == (clk[p] % SendPoint = 0) /\ (clk[p] % PredictPoint # 0)

\* Predicate indicating that p should perform a Predict action
IsPredict(p) == (clk[p] % PredictPoint = 0) /\ (clk[p] % SendPoint # 0)

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk       = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send action for a process p
\* ----------------------------------------------------------------------
Send(p) ==
    /\ IsSend(p)
    /\ outbox' = [outbox EXCEPT ![p] = 
                     { [type |-> "alive", src |-> p, dst |-> q] : q \in Proc \ {p} } ]
    /\ clk'       = [clk EXCEPT ![p] = NewClk(p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1 
                                          : q \in Proc \ {p}]
    /\ UNCHANGED <<suspicion, timeout>>

\* ----------------------------------------------------------------------
\* Predict action for a process p
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ IsPredict(p)
    /\ let newSus == { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clk'       = [clk EXCEPT ![p] = NewClk(p)]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = @ + 1 
                                          : q \in Proc \ {p}]
    /\ UNCHANGED <<timeout, outbox>>

\* ----------------------------------------------------------------------
\* Receive action for a process p
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ ~IsSend(p) /\ ~IsPredict(p)
    \* Determine which alive messages addressed to p are currently in any outbox
    /\ let msgs == { m \in UNION { outbox[r] : r \in Proc } : 
                     /\ m.type = "alive"
                     /\ m.dst = p } in
       Recvd == { m.src : m \in msgs }
    /\ \* Update lastHeard, suspicion and timeout according to received messages
       lastHeard' = [lastHeard EXCEPT ![p][src] = 
                        IF src \in Recvd THEN 0 ELSE @
                        : src \in Proc \ {p}]
    /\ suspicion' = [suspicion EXCEPT ![p] = 
                        suspicion[p] \ Recvd]
    /\ timeout' = [timeout EXCEPT 
                        ![p][src] = 
                           IF src \in Recvd /\ src \in suspicion[p] 
                               THEN @ + 1 
                               ELSE @
                       : src \in Proc \ {p}]
    /\ \* Remove the delivered messages from all outboxes
       outbox' = [r \in Proc |-> outbox[r] \ { m \in outbox[r] : m.dst = p }]
    /\ clk' = [clk EXCEPT ![p] = NewClk(p)]
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [] [Next]_<<suspicion, timeout, lastHeard, clk, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : suspicion[p] \subseteq Proc \ {p}
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : timeout[p][q] \in Nat
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : lastHeard[p][q] \in Nat
    /\ clk       \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Operators required by the configuration file
\* ----------------------------------------------------------------------
SPECIFICATION == Spec
INIT          == Init
NEXT          == Next
INVARIANTS    == TypeOK
PROPERTIES    == TRUE

====