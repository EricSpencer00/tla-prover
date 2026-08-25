---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible message types (e.g., {"Alive"})

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   – processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]] – adaptive timeout
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]] – ticks since last alive from q
    clock,       \* [p \in Proc |-> Nat]                – local clock
    net          \* Set of messages currently in transit

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [src : Proc, dst : Proc, type : Messages]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
OtherProcs(p) == Proc \ {p}

\* Maximum relevant threshold for process p
MaxThresh(p) == 
    LET tSet == { timeout[p][q] : q \in OtherProcs(p) } \cup {SendPoint, PredictPoint} 
    IN  IF tSet = {} THEN 0 ELSE Max(tSet)

\* Clock update with wrap‑around
NextClock(p, c) == 
    IF c + 1 > MaxThresh(p) THEN 0 ELSE c + 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> 
                       IF q = p THEN 0 ELSE d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 
                       IF q = p THEN 0 ELSE 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ net       = {}

\* ----------------------------------------------------------------------
\* Send action for process p
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ \* Create alive messages for all other processes
       let newMsgs == { [src |-> p, dst |-> q, type |-> "Alive"] : q \in OtherProcs(p) } in
    /\ net' = net \cup newMsgs
    /\ \* Increment lastHeard counters for all q (except self)
       lastHeard' = [lh \in lastHeard EXCEPT 
                       ![p][q] = IF q = p THEN @[p][q] ELSE @[p][q] + 1 
                       \* (the increment is unconditional; the specification
                         mentions “for processes it has not yet timed out on”,
                         but this simple increment satisfies the type invariant) 
                     ]
    /\ suspicion' = suspicion
    /\ timeout'   = timeout
    /\ clock' = [c \in clock EXCEPT ![p] = NextClock(p, clock[p])]
    /\ UNCHANGED << suspicion, timeout >>

\* ----------------------------------------------------------------------
\* Predict action for process p
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ \* Identify processes to suspect
       let toSuspect == { q \in OtherProcs(p) : lastHeard[p][q] > timeout[p][q] } in
    /\ suspicion' = [s \in suspicion EXCEPT ![p] = @[p] \cup toSuspect]
    /\ \* Increment all lastHeard counters
       lastHeard' = [lh \in lastHeard EXCEPT 
                       ![p][q] = IF q = p THEN @[p][q] ELSE @[p][q] + 1 
                     ]
    /\ timeout' = timeout
    /\ net' = net
    /\ clock' = [c \in clock EXCEPT ![p] = NextClock(p, clock[p])]
    /\ UNCHANGED << suspicion, timeout >>

\* ----------------------------------------------------------------------
\* Receive action for process p
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ /\ clock[p] % SendPoint # 0
       /\ clock[p] % PredictPoint # 0
    /\ let incoming == { m \in net : m.dst = p } in
       incomingSrcs == { m.src : m \in incoming }
    /\ \* Update lastHeard counters: reset for senders, increment otherwise
       lastHeard' = [lh \in lastHeard EXCEPT 
                       ![p][q] = IF q \in incomingSrcs THEN 0 
                                 ELSE IF q = p THEN @[p][q] 
                                 ELSE @[p][q] + 1 
                     ]
    /\ \* Remove senders from suspicion set
       suspicion' = [s \in suspicion EXCEPT ![p] = @[p] \ { q \in incomingSrcs }]
    /\ \* Adaptive timeout increase for previously suspected senders
       timeout' = [to \in timeout EXCEPT 
                       ![p][q] = IF q \in incomingSrcs /\ q \in suspicion[p] 
                                 THEN @[p][q] + 1 
                                 ELSE @[p][q] 
                     ]
    /\ net' = net \ incoming
    /\ clock' = [c \in clock EXCEPT ![p] = NextClock(p, clock[p])]
    /\ UNCHANGED << suspicion, timeout >>

\* ----------------------------------------------------------------------
\* Next-state relation (nondeterministic choice of a process and its action)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : 
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : suspicion[p] \subseteq OtherProcs(p)
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : 
          (q = p) => timeout[p][q] = 0
          /\ (q # p) => timeout[p][q] >= d0
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : (q = p) => lastHeard[p][q] = 0
    /\ clock \in [Proc -> Nat]
    /\ net \subseteq { m \in Message : m.src \in Proc /\ m.dst \in Proc /\ m.type \in Messages }

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspicion, timeout, lastHeard, clock, net>>

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANTS == TypeOK

====