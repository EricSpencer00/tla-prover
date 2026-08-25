---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (Nat)
    SendPoint,     \* Positive integer, send interval
    PredictPoint,  \* Positive integer, predict interval
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    suspect,   \* [p \in Proc -> SUBSET Proc]   (process p's suspicion set)
    timeout,   \* [p \in Proc -> [q \in Proc -> Nat]]   (adaptive timeout intervals)
    last,      \* [p \in Proc -> [q \in Proc -> Nat]]   (ticks since last alive from q)
    clk,       \* [p \in Proc -> Nat]        (local clock of each process)
    outbox     \* [p \in Proc -> SUBSET Messages]   (messages p intends to send)

vars == << suspect, timeout, last, clk, outbox >>

\* Helper to construct an alive message from p to q
AliveMsg(p, q) == [ from |-> p, to |-> q, type |-> "alive" ]

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE 0]]
    /\ clk     = [p \in Proc |-> 0]
    /\ outbox  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ clk     \in [Proc -> Nat]
    /\ outbox  \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Send action (alive broadcast)
Send(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \cup { AliveMsg(p,q) : q \in Proc \ {p} }]
    /\ clk'    = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last'   = [last EXCEPT ![p] =
                     [q \in Proc |-> 
                        IF q = p THEN last[p][q]
                        ELSE IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                        ELSE last[p][q] ]]
    /\ UNCHANGED << suspect, timeout >>

\* ----------------------------------------------------------------------
\* Predict action (suspicion update)
Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
                        { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ clk'    = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last'   = [last EXCEPT ![p] =
                     [q \in Proc |-> 
                        IF q = p THEN last[p][q]
                        ELSE last[p][q] + 1 ]]
    /\ UNCHANGED << timeout, outbox >>

\* ----------------------------------------------------------------------
\* Receive action (handle incoming alive messages)
Receive(p) ==
    /\ clk[p] % SendPoint # 0
    /\ clk[p] % PredictPoint # 0
    \* Non‑deterministically choose a subset of alive messages addressed to p
    \E R \subseteq { AliveMsg(q, p) : q \in Proc \ {p} } :
        /\ outbox' = outbox
        /\ clk'    = [clk EXCEPT ![p] = clk[p] + 1]

        /\ last'   = [last EXCEPT ![p] =
                         [q \in Proc |-> 
                            IF q = p THEN last[p][q]
                            ELSE IF \E m \in R : m.from = q THEN 0
                            ELSE last[p][q] + 1 ]]

        /\ suspect' = [suspect EXCEPT ![p] =
                         (suspect[p] \ { q \in Proc \ {p} : \E m \in R : m.from = q })
                         \cup { q \in Proc \ {p} : 
                                 (q \notin { m.from : m \in R }) /\ last[p][q] > timeout[p][q] }]

        /\ timeout' = [timeout EXCEPT ![p] =
                         [q \in Proc |-> 
                            IF q = p THEN timeout[p][q]
                            ELSE IF q \in suspect[p] /\ \E m \in R : m.from = q
                                 THEN timeout[p][q] + 1
                                 ELSE timeout[p][q] ]]

\* ----------------------------------------------------------------------
\* The Next-state relation: one process makes a step
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* The set of properties required by the configuration file
\* (only the invariant is required here)
THEOREM Spec => []TypeOK

====