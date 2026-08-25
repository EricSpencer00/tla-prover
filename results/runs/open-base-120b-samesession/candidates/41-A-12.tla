---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer send interval
    PredictPoint,  \* Positive integer predict interval (not a multiple of SendPoint)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    clock,        \* [p \in Proc -> Nat]  local clock for each process
    timeout,      \* [<<p,q>> \in Proc \X Proc -> Nat] adaptive timeout intervals
    last,         \* [<<p,q>> \in Proc \X Proc -> Nat] ticks since last heard
    suspicion,    \* [p \in Proc -> SUBSET Proc] current suspicion sets
    out           \* [p \in Proc -> SUBSET Messages] outgoing messages to be sent

\* ----------------------------------------------------------------------
\* Helper definitions
MsgAlive(p, q) == [type |-> "alive", from |-> p, to |-> q]

AllAliveMsgs(p) == { MsgAlive(p, q) : q \in Proc \ {p} }

RecvSet(p) == { m \in Messages : m.type = "alive" /\ m.to = p /\ m.from \in Proc \ {p} }

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [<<p,q>> \in Proc \X Proc |-> IF p = q THEN 0 ELSE d0]
    /\ last = [<<p,q>> \in Proc \X Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send action for process p
Send(p) ==
    /\ (clock[p] % SendPoint) = 0
    /\ (clock[p] % PredictPoint) # 0
    /\ out' = [out EXCEPT ![p] = AllAliveMsgs(p)]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p, q] = 
                IF last[p,q] < timeout[p,q] 
                THEN last[p,q] + 1 
                ELSE last[p,q] 
                FOR q \in Proc \ {p}]
    /\ suspicion' = suspicion

\* ----------------------------------------------------------------------
\* Predict action for process p
Predict(p) ==
    /\ (clock[p] % PredictPoint) = 0
    /\ (clock[p] % SendPoint) # 0
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ timeout' = timeout
    /\ out' = out
    /\ last' = [last EXCEPT ![p, q] = 
                IF last[p,q] < timeout[p,q] 
                THEN last[p,q] + 1 
                ELSE last[p,q] 
                FOR q \in Proc \ {p}]
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup 
                     { q \in Proc \ {p} : last[p,q] > timeout[p,q] }]

\* ----------------------------------------------------------------------
\* Receive action for process p
Receive(p) ==
    /\ ~((clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0))
    /\ ~((clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0))
    /\ \E recv \subseteq RecvSet(p) :
        /\ out' = out
        /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
        /\ timeout' = [timeout EXCEPT 
                         ![p, q] = 
                           IF MsgAlive(q, p) \in recv /\ q \in suspicion[p]
                           THEN timeout[p,q] + 1
                           ELSE timeout[p,q] 
                       FOR q \in Proc \ {p}]
        /\ last' = [last EXCEPT 
                      ![p, q] = 
                        IF MsgAlive(q, p) \in recv
                        THEN 0
                        ELSE IF last[p,q] < timeout[p,q] 
                             THEN last[p,q] + 1 
                             ELSE last[p,q] 
                  FOR q \in Proc \ {p}]
        /\ suspicion' = [suspicion EXCEPT 
                           ![p] = suspicion[p] \ { q \in Proc \ {p} : MsgAlive(q, p) \in recv }]

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Variables tuple for stuttering steps
vars == <<clock, timeout, last, suspicion, out>>

\* ----------------------------------------------------------------------
\* Specification
Specification == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc \X Proc -> Nat]
    /\ last \in [Proc \X Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ out \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : suspicion[p] \subseteq Proc \ {p}
    /\ \A <<p,q>> \in Proc \X Proc : p # q => timeout[p,q] >= 1

\* ----------------------------------------------------------------------
\* Additional (empty) property placeholder
Properties == TRUE

=============================================================================