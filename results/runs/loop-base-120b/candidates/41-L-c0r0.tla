---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of all possible messages (records with fields type, src, dst)

VARIABLES
    suspicion,   \* [p \in Proc -> SUBSET Proc]   (process p's suspicion set)
    timeout,     \* [p \in Proc -> [q \in Proc -> Nat]] (timeout intervals)
    lastHeard,   \* [p \in Proc -> [q \in Proc -> Nat]] (ticks since last alive from q)
    clock,       \* [p \in Proc -> Nat]            (local clock of each process)
    outbox       \* [p \in Proc -> SUBSET Messages] (messages p wants to send)

\*=====================================================================
\* Helper definitions
\*=====================================================================
AliveMsg(p, q) == [type |-> "alive", src |-> p, dst |-> q]

\*=====================================================================
\* Initial state
\*=====================================================================
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\*=====================================================================
\* Send-alive action for a process p
\*=====================================================================
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMsg(p, q) : q \in Proc \ {p} }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] =
            IF q # p /\ lastHeard[p][q] < timeout[p][q]
               THEN lastHeard[p][q] + 1
               ELSE lastHeard[p][q] ]
    /\ UNCHANGED << suspicion, timeout >>

\*=====================================================================
\* Predict (suspicion) action for a process p
\*=====================================================================
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup
                     { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }]
    /\ clock'     = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] =
            IF q # p /\ lastHeard[p][q] < timeout[p][q]
               THEN lastHeard[p][q] + 1
               ELSE lastHeard[p][q] ]
    /\ UNCHANGED << outbox, timeout >>

\*=====================================================================
\* Receive action for a process p
\*=====================================================================
Receive(p) ==
    \E R \subseteq Messages :
        /\ \A m \in R : m.type = "alive" /\ m.dst = p
        LET RecvSrcs == { m.src : m \in R } IN
        /\ outbox' = outbox
        /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
        /\ lastHeard' = [lastHeard EXCEPT ![p][q] =
                IF q \in RecvSrcs
                   THEN 0
                   ELSE IF lastHeard[p][q] < timeout[p][q]
                           THEN lastHeard[p][q] + 1
                           ELSE lastHeard[p][q] ]
        /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ RecvSrcs]
        /\ timeout'   = [timeout EXCEPT ![p][q] =
                IF q \in RecvSrcs /\ q \in suspicion[p]
                   THEN timeout[p][q] + 1
                   ELSE timeout[p][q] ]
        /\ UNCHANGED << outbox, clock, lastHeard, suspicion, timeout >>

\*=====================================================================
\* Next-state relation
\*=====================================================================
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, outbox>>

\*=====================================================================
\* The required identifiers
\*=====================================================================
INIT == Init
NEXT == Next
INVARIANTS == TypeOK

====