---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer interval for sending alive messages
    PredictPoint,  \* Positive integer interval for making predictions
    Messages       \* Set of all possible alive messages (payload not used)

\* --- Variables ----------------------------------------------------
VARIABLES
    clock,        \* [p \in Proc -> Nat]   local clock per process
    timeout,      \* [p \in Proc -> [q \in Proc -> Nat]]  adaptive timeout intervals
    last,         \* [p \in Proc -> [q \in Proc -> Nat]]  ticks since last alive from q
    suspicion,   \* [p \in Proc -> SUBSET Proc]            current suspicion sets
    outMsgs       \* [p \in Proc -> SUBSET Messages]        outgoing messages

\* --- Helper definitions -------------------------------------------
ProcSet == Proc

\* Alive message addressed to a particular receiver
AliveMsg(p, r) == [type |-> "Alive", sender |-> p, dest |-> r]

\* The set of all alive messages that could be sent from any process to any other
AllAliveMsgs == { AliveMsg(p, r) : p \in Proc, r \in Proc, p # r }

\* Initial state ----------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF p # q THEN d0 ELSE 0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> IF p # q THEN 0 ELSE 0]]
    /\ suspicion = [p \in Proc |-> {}]
    /\ outMsgs = [p \in Proc |-> {}]

\* --- Actions -------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0          \* not a predict tick
    /\ outMsgs' = [outMsgs EXCEPT ![p] = { AliveMsg(p, r) : r \in Proc, r # p }]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ last' = [last EXCEPT ![p][q] = IF q # p THEN @ + 1 ELSE @]
    /\ timeout' = timeout
    /\ suspicion' = suspicion
    /\ UNCHANGED << >>                     \* all other variables unchanged

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0             \* not a send tick
    /\ \A q \in Proc \ {p}:
          IF last[p][q] > timeout[p][q]
          THEN suspicion'[p] = suspicion[p] \cup {q}
          ELSE suspicion'[p] = suspicion[p] \ {q}
    /\ last' = [last EXCEPT ![p][q] = @ + 1 | q \in Proc \ {p}]
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ timeout' = timeout
    /\ outMsgs' = outMsgs
    /\ UNCHANGED << >>

\* Receive messages addressed to p
Receive(p) ==
    /\ \E msgs \in outMsgs[p] : \A m \in msgs :
          /\ m.type = "Alive"
          /\ m.dest = p
    /\ \A q \in Proc \ {p} :
          IF \E m \in outMsgs[q] : /\ m.type = "Alive" /\ m.dest = p
          THEN /\ last'    = [last EXCEPT ![p][q] = 0]
               /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ {q}]
               /\ timeout'  = IF q \in suspicion[p]
                              THEN [timeout EXCEPT ![p][q] = @ + 1]
                              ELSE timeout
          ELSE /\ last'    = [last EXCEPT ![p][q] = @ + 1]
               /\ UNCHANGED << suspicion, timeout >>
    /\ clock' = [clock EXCEPT ![p] = @ + 1]
    /\ outMsgs' = outMsgs
    /\ UNCHANGED << >>

\* Clock wrap‑around when it exceeds all relevant thresholds
ResetClock(p) ==
    /\ clock[p] > Max({SendPoint, PredictPoint} \cup
                     { timeout[p][q] : q \in Proc \ {p} })
    /\ clock' = [clock EXCEPT ![p] = 0]
    /\ UNCHANGED << timeout, last, suspicion, outMsgs >>

\* Combined next‑state relation
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ \E p \in Proc : ResetClock(p)

\* --- Specification -------------------------------------------------
Spec == Init /\ [][Next]_<<clock, timeout, last, suspicion, outMsgs>>

\* --- Type invariant ------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ outMsgs \in [Proc -> SUBSET Messages]

\* --- Exported identifiers -------------------------------------------
INIT    == Init
NEXT    == Next
INVARIANT TypeOK

====