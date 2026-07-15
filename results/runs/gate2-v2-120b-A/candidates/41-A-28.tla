---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer, not a multiple of PredictPoint)
    PredictPoint,  \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages       \* Set of possible message records

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    Suspects,      \* [p \in Proc |-> SUBSET Proc] – suspicion set for each process
    Timeout,       \* [p \in Proc |-> [q \in Proc |-> Nat]] – timeout interval for each pair
    Counter,       \* [p \in Proc |-> [q \in Proc |-> Nat]] – ticks since last alive from q at p
    Clock,         \* [p \in Proc |-> Nat] – local clock of each process
    OutMsgs        \* [p \in Proc |-> SUBSET Messages] – outgoing messages of each process

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Alive messages are a subset of the user‑provided Messages set.
\* For clarity we assume each alive message contains a sender field.
AliveMsg(s) == { m \in Messages : m["type"] = "Alive" /\ m["sender"] = s }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Suspects = [p \in Proc |-> {}]
    /\ Timeout  = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ Counter  = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock    = [p \in Proc |-> 0]
    /\ OutMsgs  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Process actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ \E pc \in Nat :
         /\ Clock[p] % SendPoint = 0
         /\ Clock[p] % PredictPoint # 0
    /\ \A q \in Proc :
         IF q # p THEN OutMsgs' = [OutMsgs EXCEPT ![p] = OutMsgs[p] \cup AliveMsg(p)]
         ELSE OutMsgs' = OutMsgs
    /\ Counter' = [Counter EXCEPT ![p][q] = Counter[p][q] + 1
                              ![p][p] = Counter[p][p]]   \* self‑counter stays unchanged
    /\ Clock'   = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ Suspects' = Suspects
    /\ Timeout'  = Timeout
    /\ UNCHANGED << >>   \* no other variable changes

Predict(p) ==
    /\ \E pc \in Nat :
         /\ Clock[p] % PredictPoint = 0
         /\ Clock[p] % SendPoint # 0
    /\ Suspects' = [Suspects EXCEPT ![p] = { q \in Proc :
                                   \/ q \in Suspects[p]
                                      \/ Counter[p][q] > Timeout[p][q] } ]
    /\ Counter'  = [Counter EXCEPT ![p][q] = Counter[p][q] + 1
                                   ![p][p] = Counter[p][p]]
    /\ Clock'    = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ OutMsgs'  = OutMsgs
    /\ Timeout'  = Timeout
    /\ UNCHANGED << >>

Receive(p) ==
    /\ ~ (Clock[p] % SendPoint = 0 /\ Clock[p] % PredictPoint # 0)
    /\ ~ (Clock[p] % PredictPoint = 0 /\ Clock[p] % SendPoint # 0)
    /\ \A m \in OutMsgs[p] :
         IF m["type"] = "Alive" THEN
            LET s == m["sender"] IN
               /\ Counter'  = [Counter EXCEPT ![p][s] = 0]
               /\ Suspects' = [Suspects EXCEPT ![p] = Suspects[p] \ {s}]
               /\ Timeout'  = [Timeout EXCEPT
                                   ![p][s] = IF s \in Suspects[p] THEN Timeout[p][s] + 1
                                             ELSE Timeout[p][s]]
         ELSE
            Counter' = Counter
    /\ Clock'    = [Clock EXCEPT ![p] = IF Clock[p] + 1 > Max({SendPoint, PredictPoint} \cup
                                                              {Timeout[p][q] : q \in Proc})
                                 THEN 0 ELSE Clock[p] + 1]
    /\ OutMsgs'  = [OutMsgs EXCEPT ![p] = {}]   \* all messages are consumed this step
    /\ Suspects' = Suspects
    /\ Timeout'  = Timeout
    /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Global next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<Suspects, Timeout, Counter, Clock, OutMsgs>>

\* ----------------------------------------------------------------------
\* Safety invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Suspects \in [Proc -> SUBSET Proc]
    /\ Timeout  \in [Proc -> [Proc -> Nat]]
    /\ Counter  \in [Proc -> [Proc -> Nat]]
    /\ Clock    \in [Proc -> Nat]
    /\ OutMsgs  \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Exported identifiers
\* ----------------------------------------------------------------------
InitInv   == Init
NextStep  == Next
Invariant == TypeOK

====