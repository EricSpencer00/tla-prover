---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Period for sending alive messages (positive integer)
    PredictPoint,  \* Period for making predictions (positive integer)
    Messages       \* Set of possible messages

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
Message == [type : {"alive"}, src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* State Variables
\* ----------------------------------------------------------------------
VARIABLES 
    clock,    \* [p \\in Proc |-> Nat]  local clocks
    timeout,  \* [p \\in Proc |-> [q \\in Proc |-> Nat]]  timeout intervals per pair
    last,     \* [p \\in Proc |-> [q \\in Proc |-> Nat]]  ticks since last heard
    suspect,  \* [p \\in Proc |-> SUBSET Proc]           suspicion sets
    out       \* [p \\in Proc |-> SUBSET Message]        outgoing messages

\* ----------------------------------------------------------------------
\* Helper predicates
\* ----------------------------------------------------------------------
IsSend(p)    == (clock[p] % SendPoint = 0) /\ (clock[p] % PredictPoint # 0)
IsPredict(p) == (clock[p] % PredictPoint = 0) /\ (clock[p] % SendPoint # 0)

\* The maximum clock value before resetting (conservative bound)
MaxClock == Max({SendPoint, PredictPoint})

ResetClock(c) == IF c + 1 > MaxClock THEN 0 ELSE c + 1

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \\in Proc |-> 0]
    /\ timeout = [p \\in Proc |-> [q \\in Proc |-> IF p # q THEN d0 ELSE 0]]
    /\ last = [p \\in Proc |-> [q \\in Proc |-> 0]]
    /\ suspect = [p \\in Proc |-> {}]
    /\ out = [p \\in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions for a single process
\* ----------------------------------------------------------------------
Send(p) ==
    /\ out' = [out EXCEPT ![p] = 
                { [type |-> "alive", src |-> p, dst |-> q] : q \\in Proc \\ {p} }]
    /\ clock' = [clock EXCEPT ![p] = ResetClock(clock[p])]
    /\ last' = [last EXCEPT ![p][q] = 
                IF q # p /\ q \\notin suspect[p] THEN last[p][q] + 1 ELSE last[p][q] 
                \* counters for non‑suspected processes are incremented
                ]
    /\ UNCHANGED <<timeout, suspect>>

Predict(p) ==
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \cup
        { q \\in Proc \\ {p} : last[p][q] > timeout[p][q] }]
    /\ clock' = [clock EXCEPT ![p] = ResetClock(clock[p])]
    /\ last' = [last EXCEPT ![p][q] = last[p][q] + 1]
    /\ UNCHANGED <<timeout, out>>

Receive(p) ==
    LET
        Incoming == { m \\in UNION { out[q] : q \\in Proc } : m.dst = p }
        Senders  == { m.src : m \\in Incoming }
    IN
    /\ out' = [out EXCEPT ![q] = out[q] \\ { m \\in out[q] : m.dst = p } 
                \* remove all messages addressed to p
                ]
    /\ clock' = [clock EXCEPT ![p] = ResetClock(clock[p])]
    /\ last' = [last EXCEPT ![p][s] = IF s \\in Senders THEN 0 ELSE last[p][s]]
    /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \\ Senders]
    /\ timeout' = [timeout EXCEPT ![p][s] = 
                    IF s \\in Senders /\ s \\in suspect[p] 
                    THEN timeout[p][s] + 1 
                    ELSE timeout[p][s]]
    /\ UNCHANGED <<clock \\except [p = p], timeout \\except [p = p],
                   last \\except [p = p], suspect \\except [p = p]>>  \* other processes unchanged

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving of one process action)
\* ----------------------------------------------------------------------
Next ==
    \E p \\in Proc :
        \/ (IsSend(p)    /\ Send(p))
        \/ (IsPredict(p) /\ Predict(p))
        \/ (/\ ~IsSend(p) /\ ~IsPredict(p) 
            /\ Receive(p))

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<clock, timeout, last, suspect, out>>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ out \in [Proc -> SUBSET Message]
    /\ Messages = { [type |-> "alive", src |-> p, dst |-> q] : p,q \\in Proc, p # q }

\* ----------------------------------------------------------------------
\* Theorem (optional) - ensures Spec implies TypeOK invariant
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK

====