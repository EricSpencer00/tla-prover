---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,            \* Set of process identifiers
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Period for sending alive messages (positive integer)
    PredictPoint,    \* Period for making predictions (positive integer)
    Messages         \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    clk,            \* [p \in Proc -> Nat]   local clock of each process
    suspicion,      \* [p \in Proc -> SUBSET Proc]   processes suspected by p
    timeout,        \* [p \in Proc -> [q \in Proc -> Nat]]   adaptive timeout intervals
    lastHeard,      \* [p \in Proc -> [q \in Proc -> Nat]]   ticks since p last heard from q
    outbox          \* [p \in Proc -> SUBSET Messages]       messages p intends to send

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Increment last‑heard counters for all q where the counter is still below the timeout.
IncLastHeard(p) ==
    [lastHeard EXCEPT ![p] =
        [lastHeard[p] EXCEPT ![q] = 
            IF q # p /\ lastHeard[p][q] < timeout[p][q]
                THEN lastHeard[p][q] + 1
                ELSE lastHeard[p][q]]]

\* Increment last‑heard counters for all q ≠ src (src is a freshly received alive message).
IncLastHeardExcept(p, src) ==
    [lastHeard EXCEPT ![p] =
        [lastHeard[p] EXCEPT ![q] =
            IF q # p /\ q # src /\ lastHeard[p][q] < timeout[p][q]
                THEN lastHeard[p][q] + 1
                ELSE IF q = src THEN 0 ELSE lastHeard[p][q]]]

\* The set of processes that p should newly suspect during a prediction step.
NewSuspects(p) ==
    { q \in Proc : q # p /\ lastHeard[p][q] > timeout[p][q] }

\* The set of alive messages p creates when it sends.
AliveMsgs(p) ==
    { [src |-> p, dst |-> q, typ |-> "alive"] : q \in Proc \ {p} }

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ clk = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Process actions
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0               \* not a prediction step
    /\ outbox' = [outbox EXCEPT ![p] = AliveMsgs(p)]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ lastHeard' = IncLastHeard(p)
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0                  \* not a send step
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup NewSuspects(p)]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ lastHeard' = IncLastHeard(p)
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    /\ \E src \in Proc : src # p               \* assume an alive message from src arrives
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {src}]
    /\ timeout' = 
        [timeout EXCEPT ![p][src] = 
            IF src \in suspicion[p] 
                THEN timeout[p][src] + 1 
                ELSE timeout[p][src]]
    /\ lastHeard' = IncLastHeardExcept(p, src)
    /\ UNCHANGED outbox

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<clk, suspicion, timeout, lastHeard, outbox>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clk \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANTS == TypeOK

====