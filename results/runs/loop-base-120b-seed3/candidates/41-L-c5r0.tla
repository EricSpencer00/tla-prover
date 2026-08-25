---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Positive integer: period for sending alive messages
    PredictPoint,  \* Positive integer: period for making predictions
    Messages       \* Set of possible messages (supplied by the environment)

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    suspect,   \* [p \in Proc -> SUBSET Proc]  (process p's suspicion set)
    timeout,   \* [p \in Proc -> [q \in Proc -> Nat]] (timeout interval for each (p,q))
    last,      \* [p \in Proc -> [q \in Proc -> Nat]] (ticks since p last heard from q)
    clock,     \* [p \in Proc -> Nat]               (local clock of each process)
    out        \* [p \in Proc -> SUBSET Messages]   (outgoing messages of each process)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Message(p,q) == [src |-> p, dst |-> q, kind |-> "alive"]

\* Increment a clock and wrap around when it exceeds both periods
NextClock(c) == 
    IF (c + 1) > Max(SendPoint, PredictPoint) 
    THEN 0 
    ELSE c + 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init == 
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock   = [p \in Proc |-> 0]
    /\ out     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc: suspect[p] \subseteq Proc \ {p}
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc: timeout[p][q] \in Nat
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc: last[p][q] \in Nat
    /\ clock   \in [Proc -> Nat]
    /\ out     \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Actions for a single process p
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ (clock[p] \in SendPoint * Nat)          \* multiple of SendPoint
    /\ (clock[p] \notin PredictPoint * Nat)    \* not a multiple of PredictPoint
    /\ UNCHANGED suspect
    /\ UNCHANGED timeout
    /\ out' = [out EXCEPT ![p] = out[p] \cup 
                { Message(p,q) : q \in Proc \ {p} } ]
    /\ clock' = [clock EXCEPT ![p] = NextClock(clock[p])]
    /\ last' = [last EXCEPT ![p][q] = 
                 IF last[p][q] < timeout[p][q] 
                 THEN @ + 1 
                 ELSE @ 
                 \* for all q \in Proc \ {p}
               ]
    /\ UNCHANGED << >>  \* all other variables unchanged

Predict(p) ==
    /\ (clock[p] \in PredictPoint * Nat)       \* multiple of PredictPoint
    /\ (clock[p] \notin SendPoint * Nat)       \* not a multiple of SendPoint
    /\ suspect' = [suspect EXCEPT ![p] = 
        suspect[p] \cup { q \in Proc \ {p} : last[p][q] > timeout[p][q] } ]
    /\ timeout' = timeout
    /\ out' = out
    /\ clock' = [clock EXCEPT ![p] = NextClock(clock[p])]
    /\ last' = [last EXCEPT ![p][q] = 
                 IF last[p][q] < timeout[p][q] 
                 THEN @ + 1 
                 ELSE @ 
               ]
    
Receive(p) ==
    /\ (clock[p] \notin SendPoint * Nat) 
    /\ (clock[p] \notin PredictPoint * Nat)
    /\ \E recv \in SUBSET (Proc \ {p}) :
        /\ \* nondeterministically chosen set of senders whose alive messages are received this step
        /\ recv \subseteq Proc \ {p}
        /\ \* Update suspicion set, timeout interval and last‑heard counters
        /\ suspect' = [suspect EXCEPT ![p] = 
              suspect[p] \ { q \in recv } ]
        /\ timeout' = [timeout EXCEPT ![p][q] = 
              IF q \in recv /\ q \in suspect[p] 
              THEN @ + 1 
              ELSE @,
              \* for all q \in Proc
            ]
        /\ out' = out
        /\ clock' = [clock EXCEPT ![p] = NextClock(clock[p])]
        /\ last' = [last EXCEPT ![p][q] = 
              IF q \in recv 
              THEN 0 
              ELSE @,
              \* for all q \in Proc
            ]

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving of actions of any process)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : 
        \/ SendAlive(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<suspect, timeout, last, clock, out>>

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
\* Init predicate
Init == Init

\* Invariant
TypeOK == TypeOK

====