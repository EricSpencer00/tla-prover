---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Proc,          \* Set of all processes
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Interval for sending alive messages (positive integer)
    PredictPoint,  \* Interval for making predictions (positive integer)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* Message definition
Message == [type : {"Alive"}, src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    suspect,   \* [Proc -> SUBSET Proc]   : processes currently suspected
    timeout,   \* [Proc -> [Proc -> Nat]] : timeout intervals per target
    last,      \* [Proc -> [Proc -> Nat]] : ticks since last heard from each target
    clk,       \* [Proc -> Nat]           : local clock of each process
    out        \* [Proc -> SUBSET Message] : outgoing messages prepared in this step

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ clk     \in [Proc -> Nat]
    /\ out     \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE 0]]
    /\ clk     = [p \in Proc |-> 0]
    /\ out     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper predicates for clock conditions
SendCond(p)    == (clk[p] % SendPoint = 0) /\ (clk[p] % PredictPoint # 0)
PredictCond(p) == (clk[p] % PredictPoint = 0) /\ (clk[p] % SendPoint # 0)
OtherCond(p)   == ~(SendCond(p) \/ PredictCond(p))

\* ----------------------------------------------------------------------
\* Action: send alive messages
Send(p) ==
    /\ SendCond(p)
    /\ out' = [out EXCEPT ![p] = { [type |-> "Alive", src |-> p, dst |-> q] : q \in Proc \ {p} }]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last' = [last EXCEPT ![p][q] = 
                    IF q # p /\ last[p][q] < timeout[p][q] 
                    THEN last[p][q] + 1 
                    ELSE last[p][q] ]
    /\ UNCHANGED <<suspect, timeout>>

\* ----------------------------------------------------------------------
\* Action: make predictions (update suspicion set)
Predict(p) ==
    /\ PredictCond(p)
    /\ \* processes whose last‑heard counter exceeds their timeout become suspected
       suspect' = [suspect EXCEPT ![p] = suspect[p] \cup 
                    { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last' = [last EXCEPT ![p][q] = IF q # p THEN last[p][q] + 1 ELSE last[p][q]]
    /\ out' = [out EXCEPT ![p] = {}]
    /\ UNCHANGED timeout

\* ----------------------------------------------------------------------
\* Action: receive messages (abstracted)
Receive(p) ==
    /\ OtherCond(p)
    /\ \* nondeterministically choose a set of processes from which an alive
       \* message is received this step
       LET R == SUBSET (Proc \ {p}) IN
       /\ last' = [last EXCEPT 
                    ![p][q] = 
                        IF q \in R 
                        THEN 0 
                        ELSE last[p][q] + 1]
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ R]
       /\ timeout' = [timeout EXCEPT 
                       ![p][q] = IF q \in R /\ q \in suspect[p] 
                                 THEN timeout[p][q] + 1 
                                 ELSE timeout[p][q]]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ out' = [out EXCEPT ![p] = {}]
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Next-state relation (any process may take any enabled action)
Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    Init /\ [][Next]_<<suspect, timeout, last, clk, out>>

\* ----------------------------------------------------------------------
\* Invariants and properties required by the .cfg file
INVARIANTS == TypeOK
PROPERTIES == TRUE

\* ----------------------------------------------------------------------
\* Assumptions on intervals (send and predict never coincide)
ASSUME SendPredictDistinct ==
    /\ SendPoint > 0
    /\ PredictPoint > 0
    /\ SendPoint % PredictPoint # 0
    /\ PredictPoint % SendPoint # 0

====