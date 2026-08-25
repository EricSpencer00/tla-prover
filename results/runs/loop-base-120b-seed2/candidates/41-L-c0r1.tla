---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]  -- processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout intervals
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive from q
    clock,       \* [p \in Proc |-> Nat]                     -- local clock of p
    outbox       \* [p \in Proc |-> SUBSET Messages]        \* messages p wants to send

vars == << suspicion, timeout, lastHeard, clock, outbox >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveMsg(p,q) == [src |-> p, dst |-> q, type |-> "alive"]

\* The set of all alive messages that could be received by process p
IncomingAlive(p) ==
    { m \in UNION { outbox[s] : s \in Proc } :
        /\ m.dst = p
        /\ m.type = "alive"
    }

\* Update of lastHeard after a Send action
LastHeardAfterSend(p) ==
    [q \in Proc |-> 
        IF q # p /\ lastHeard[p][q] < timeout[p][q]
        THEN lastHeard[p][q] + 1
        ELSE lastHeard[p][q]]

\* Update of lastHeard after a Predict action (simply increment all counters)
LastHeardAfterPredict(p) ==
    [q \in Proc |-> lastHeard[p][q] + 1]

\* Update of lastHeard after a Receive action with a given set of senders recv
LastHeardAfterReceive(p, recv) ==
    [q \in Proc |-> IF q \in recv THEN 0 ELSE lastHeard[p][q]]

\* Update of timeout after a Receive action with a given set of senders recv
TimeoutAfterReceive(p, recv) ==
    [q \in Proc |-> 
        IF q \in recv /\ q \in suspicion[p]
        THEN timeout[p][q] + 1
        ELSE timeout[p][q]]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outbox    = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = outbox[p] \cup
                     { AliveMsg(p,q) : q \in Proc \ {p} }]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = LastHeardAfterSend(p)]
    /\ UNCHANGED << suspicion, timeout >>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT
                        ![p] = suspicion[p] \cup
                               { q \in Proc \ {p} :
                                   lastHeard[p][q] > timeout[p][q] } ]
    /\ clock'   = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p] = LastHeardAfterPredict(p)]
    /\ UNCHANGED << timeout, outbox >>

Receive(p) ==
    /\ \A sp \in {SendPoint, PredictPoint} : clock[p] % sp # 0
    /\ \* Choose nondeterministically a set of senders from which p receives an alive message
       \E recv \in SUBSET (Proc \ {p}) :
          /\ \A s \in recv : AliveMsg(s,p) \in outbox[s]   \* the message exists
          /\ lastHeard' = [lastHeard EXCEPT ![p] = LastHeardAfterReceive(p, recv)]
          /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ recv]
          /\ timeout'   = [timeout EXCEPT ![p] = TimeoutAfterReceive(p, recv)]
          /\ clock'     = [clock EXCEPT ![p] = clock[p] + 1]
          /\ UNCHANGED outbox

\* The next-state relation allows any process to take one of its enabled actions
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outbox    \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Theorem (optional) that Spec implies TypeOK invariant
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
====