---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Proc,          \* The set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of all possible messages

VARIABLES 
    clk,          \* [p \in Proc -> Nat]   local clocks
    last,         \* [p \in Proc -> [q \in Proc -> Nat]]   counters since last heard
    timeout,      \* [p \in Proc -> [q \in Proc -> Nat]]   adaptive timeout intervals
    suspect,      \* [p \in Proc -> SUBSET Proc]           suspicion sets
    out           \* [p \in Proc -> SUBSET Messages]       outgoing messages

\* ----------------------------------------------------------------------
\* Helper: maximum of a non‑empty finite set of naturals
MaxSet(S) == 
    IF S = {} THEN 0 
    ELSE LET m == CHOOSE x \in S : \A y \in S : y <= x IN m

\* Maximum relevant threshold for a process p (send, predict, and all timeouts)
MaxThreshold(p) == 
    MaxSet({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc })

\* ----------------------------------------------------------------------
\* Initial state
Init == 
    /\ clk    = [p \in Proc |-> 0]
    /\ last   = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ timeout= [p \in Proc |-> [q \in Proc |-> d0]]
    /\ suspect= [p \in Proc |-> {}]
    /\ out    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Action: send alive messages
Send(p) == 
    /\ p \in Proc
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ \* outgoing messages (the actual content is left to the controller)
       out' = [out EXCEPT ![p] = {}]
    /\ suspect' = suspect
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p][q] = 
                IF last[p][q] < timeout[p][q] 
                THEN last[p][q] + 1 
                ELSE last[p][q] 
                \* for all q \in Proc
               ]
    /\ clk' = [clk EXCEPT ![p] = 
                IF clk[p] + 1 > MaxThreshold(p) 
                THEN 0 
                ELSE clk[p] + 1
               ]

\* ----------------------------------------------------------------------
\* Action: make predictions (update suspicion set)
Predict(p) == 
    /\ p \in Proc
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT 
                    ![p] = suspect[p] 
                           \cup { q \in Proc : q # p /\ last[p][q] > timeout[p][q] } ]
    /\ out' = out
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p][q] = 
                IF last[p][q] < timeout[p][q] 
                THEN last[p][q] + 1 
                ELSE last[p][q] 
               ]
    /\ clk' = [clk EXCEPT ![p] = 
                IF clk[p] + 1 > MaxThreshold(p) 
                THEN 0 
                ELSE clk[p] + 1
               ]

\* ----------------------------------------------------------------------
\* Action: receive incoming alive messages (nondeterministic subset)
Receive(p) == 
    /\ p \in Proc
    /\ \* not a send step and not a predict step
       ~(clk[p] % SendPoint = 0 /\ clk[p] % PredictPoint # 0)
       /\ ~(clk[p] % PredictPoint = 0 /\ clk[p] % SendPoint # 0)
    /\ recvSet \in SUBSET (Proc \ {p})   \* processes from which p receives an alive message this step
    /\ out' = out
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ { q \in recvSet } ]
    /\ timeout' = [timeout EXCEPT 
                    ![p][q] = IF q \in recvSet /\ q \in suspect[p] 
                               THEN timeout[p][q] + 1 
                               ELSE timeout[p][q] 
                  ]
    /\ last' = [last EXCEPT 
                ![p][q] = IF q \in recvSet 
                           THEN 0 
                           ELSE IF last[p][q] < timeout[p][q] 
                                 THEN last[p][q] + 1 
                                 ELSE last[p][q] 
               ]
    /\ clk' = [clk EXCEPT ![p] = 
                IF clk[p] + 1 > MaxThreshold(p) 
                THEN 0 
                ELSE clk[p] + 1
               ]

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving semantics: one process acts at a time)
Next == 
    \E p \in Proc : \/ Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK == 
    /\ clk    \in [Proc -> Nat]
    /\ last   \in [Proc -> [Proc -> Nat]]
    /\ timeout\in [Proc -> [Proc -> Nat]]
    /\ suspect\in [Proc -> SUBSET Proc]
    /\ out    \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification (used by the .cfg file)
Spec == Init /\ [][Next]_<<clk, last, timeout, suspect, out>>

====