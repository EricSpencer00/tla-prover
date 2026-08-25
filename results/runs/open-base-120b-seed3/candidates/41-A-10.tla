---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Positive integer send interval
    PredictPoint,  \* Positive integer predict interval
    Messages       \* Set of possible messages

\* ----------------------------------------------------------------------
\* Message definition (only alive messages are used)
Message == [type : {"alive"}, from : Proc, to : Proc]

AliveMsg(p,q) == [type |-> "alive", from |-> p, to |-> q]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    clock,    \* [p \in Proc -> Nat]   local clocks
    suspect,  \* [p \in Proc -> SUBSET Proc]   suspicion sets
    timeout,  \* [p \in Proc -> [q \in Proc -> Nat]]   adaptive timeouts
    lhc,      \* [p \in Proc -> [q \in Proc -> Nat]]   last‑heard counters
    out       \* [p \in Proc -> SUBSET Messages]      outgoing messages

vars == <<clock, suspect, timeout, lhc, out>>

\* ----------------------------------------------------------------------
\* Helper definitions
IsSend(i) ==
    (clock[i] % SendPoint = 0) /\ (clock[i] % PredictPoint # 0)

IsPredict(i) ==
    (clock[i] % PredictPoint = 0) /\ (clock[i] % SendPoint # 0)

\* Increment counters for all processes that have not yet timed out
IncCounters(i, lc) ==
    [j \in Proc |-> IF lc[i][j] < timeout[i][j] THEN lc[i][j] + 1 ELSE lc[i][j]]

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lhc = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send alive messages
SendAlive(i) ==
    /\ IsSend(i)
    /\ out' = [out EXCEPT ![i] = { AliveMsg(i,j) : j \in Proc \ {i} } ]
    /\ clock' = [clock EXCEPT ![i] = clock[i] + 1]
    /\ lhc' = [lhc EXCEPT ![i] = IncCounters(i, lhc)]
    /\ UNCHANGED <<suspect, timeout>>

\* ----------------------------------------------------------------------
\* Make predictions (suspicion updates)
Predict(i) ==
    /\ IsPredict(i)
    /\ suspect' = [suspect EXCEPT ![i] =
          suspect[i] \cup
          { j \in Proc \ {i} : lhc[i][j] > timeout[i][j] } ]
    /\ clock' = [clock EXCEPT ![i] = clock[i] + 1]
    /\ lhc' = [lhc EXCEPT ![i] = IncCounters(i, lhc)]
    /\ UNCHANGED <<out, timeout>>

\* ----------------------------------------------------------------------
\* Receive messages (nondeterministic set of incoming alive messages)
Receive(i) ==
    /\ ~IsSend(i) /\ ~IsPredict(i)
    /\ \* Receiver may get any subset of alive messages addressed to i
       LET recv == { m \in Messages : 
                      /\ m.type = "alive"
                      /\ m.to = i
                      /\ m.from \in Proc } IN
    /\ \* Update last‑heard counters, suspicion set and adaptive timeout
       out' = out
    /\ clock' = [clock EXCEPT ![i] = clock[i] + 1]
    /\ lhc' = [lhc EXCEPT ![i][j] = 
                IF \E m \in recv : m.from = j
                THEN 0
                ELSE IncCounters(i, lhc)[i][j] ]
    /\ suspect' = [suspect EXCEPT ![i] = 
                { j \in suspect[i] :
                    \A m \in recv : m.from # j } ]
    /\ timeout' = [timeout EXCEPT ![i][j] = 
                IF \E m \in recv : m.from = j /\ j \in suspect[i]
                THEN timeout[i][j] + 1
                ELSE timeout[i][j] ]
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* A single process step (interleaving semantics)
ProcStep ==
    \E i \in Proc :
        \/ SendAlive(i)
        \/ Predict(i)
        \/ Receive(i)

Next ==
    ProcStep

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lhc \in [Proc -> [Proc -> Nat]]
    /\ out \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Required identifiers for the configuration
INIT == Init
NEXT == Next
INVARIANTS == TypeOK
PROPERTIES == TRUE

====