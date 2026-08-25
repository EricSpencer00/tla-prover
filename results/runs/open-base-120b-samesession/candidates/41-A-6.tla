---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Interval for sending alive messages (positive integer)
    PredictPoint,  \* Interval for making predictions (positive integer)
    Messages       \* Set of possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    clock,        \* [p \in Proc |-> Nat]  local logical clock of each process
    timeout,      \* [p \in Proc |-> [q \in Proc |-> Nat]]  adaptive timeout for each (p,q)
    lastHeard,    \* [p \in Proc |-> [q \in Proc |-> Nat]]  ticks since p last heard from q
    suspicion,    \* [p \in Proc |-> SUBSET Proc]          set of processes p suspects
    outbox        \* [p \in Proc |-> SUBSET Messages]     messages p intends to send

vars == <<clock, timeout, lastHeard, suspicion, outbox>>

\* ----------------------------------------------------------------------
\* Message definition (alive messages)
\* ----------------------------------------------------------------------
AliveMessage(p,q) == [type |-> "alive", src |-> p, dst |-> q]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ClockReset(p) ==
    LET next == clock[p] + 1 IN
    LET maxTimeout == Max({ SendPoint, PredictPoint } \cup
                          { timeout[p][q] : q \in Proc }) IN
    IF next > maxTimeout THEN 0 ELSE next

IncLastHeard(p, q) ==
    IF lastHeard[p][q] < timeout[p][q] THEN lastHeard[p][q] + 1
    ELSE lastHeard[p][q]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ suspicion = [p \in Proc |-> {}]
    /\ outbox = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Process actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outbox' = [outbox EXCEPT ![p] = { AliveMessage(p,q) : q \in Proc \ {p} }]
    /\ clock' = [clock EXCEPT ![p] = ClockReset(p)]
    /\ lastHeard' = [lastHeard EXCEPT
                      ![p][q] = IncLastHeard(p,q)  \* only for non‑timed‑out partners
                    ]
    /\ UNCHANGED <<timeout, suspicion>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT
                       ![p] = suspicion[p] \cup
                              { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] }
                     ]
    /\ clock' = [clock EXCEPT ![p] = ClockReset(p)]
    /\ lastHeard' = [lastHeard EXCEPT
                       ![p][q] = lastHeard[p][q] + 1
                     ]
    /\ UNCHANGED <<timeout, outbox>>

Receive(p) ==
    \E recv \in SUBSET Messages :
        /\ \A m \in recv : /\ m.type = "alive"
                           /\ m.dst = p
                           /\ m.src \in Proc \ {p}
        /\ outbox' = outbox
        /\ clock' = [clock EXCEPT ![p] = ClockReset(p)]
        /\ lastHeard' = [lastHeard EXCEPT
                           ![p][q] = IF \E m \in recv : m.src = q
                                        THEN 0
                                        ELSE lastHeard[p][q] + 1
                         ]
        /\ suspicion' = [suspicion EXCEPT
                           ![p] = suspicion[p] \ { q \in Proc \ {p} :
                                                    \E m \in recv : m.src = q }
                         ]
        /\ timeout' = [timeout EXCEPT
                         ![p][q] = IF \E m \in recv :
                                      /\ m.src = q
                                      /\ q \in suspicion[p]
                                   THEN timeout[p][q] + 1
                                   ELSE timeout[p][q]
                       ]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ outbox \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification and auxiliary operators required by the .cfg file
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_vars

INVARIANTS == TypeOK

PROPERTIES == TRUE

=============================================================================