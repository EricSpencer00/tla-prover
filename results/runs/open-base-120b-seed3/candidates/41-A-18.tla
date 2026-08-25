---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages

VARIABLES 
    suspect,   \* [Proc -> SUBSET Proc]   suspicion sets per process
    timeout,   \* [Proc -> [Proc -> Nat]] timeout intervals per process pair
    last,      \* [Proc -> [Proc -> Nat]] counters since last heard
    clock,     \* [Proc -> Nat]          local clocks
    outbox     \* [Proc -> SUBSET Messages]   messages to be sent

\*--------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------

MaxAll(p) == 
    Max( {SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc } )

ClockInc(p) == 
    IF clock[p] + 1 > MaxAll(p) THEN 0 ELSE clock[p] + 1

\*--------------------------------------------------------------
\* Initialization
\*--------------------------------------------------------------

Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock   = [p \in Proc |-> 0]
    /\ outbox  = [p \in Proc |-> {}]

\*--------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------

TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ clock   \in [Proc -> Nat]
    /\ outbox  \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : \A q \in Proc : timeout[p][q] >= 0 /\ last[p][q] >= 0

\*--------------------------------------------------------------
\* Actions
\*--------------------------------------------------------------

Send(p) ==
    /\ (clock[p] % SendPoint) = 0
    /\ (clock[p] % PredictPoint) # 0
    /\ outbox' = [outbox EXCEPT ![p] = 
                    { [src |-> p, dst |-> q, kind |-> "alive"] : q \in Proc \ {p} } ]
    /\ clock' = [clock EXCEPT ![p] = ClockInc(p)]
    /\ suspect' = suspect
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p] = 
                 [last[p] EXCEPT ![q] = 
                    IF last[p][q] < timeout[p][q] 
                    THEN last[p][q] + 1 
                    ELSE last[p][q] ] ] 
    /\ UNCHANGED <<suspect, timeout>>

Predict(p) ==
    /\ (clock[p] % PredictPoint) = 0
    /\ (clock[p] % SendPoint) # 0
    /\ suspect' = [suspect EXCEPT ![p] = 
                    suspect[p] \cup 
                    { q \in Proc \ {p} : last[p][q] > timeout[p][q] } ]
    /\ clock' = [clock EXCEPT ![p] = ClockInc(p)]
    /\ timeout' = timeout
    /\ outbox' = outbox
    /\ last' = [last EXCEPT ![p] = 
                 [last[p] EXCEPT ![q] = 
                    IF last[p][q] < timeout[p][q] 
                    THEN last[p][q] + 1 
                    ELSE last[p][q] ] ] 
    /\ UNCHANGED <<suspect, timeout>>

Receive(p) ==
    \E recv \subseteq { m \in Messages : m.dst = p /\ m.kind = "alive" } :
      LET recSrcs == { m.src : m \in recv } IN
        /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ recSrcs]
        /\ timeout' = [timeout EXCEPT ![p] = 
                        [timeout[p] EXCEPT ![q] = 
                           IF q \in recSrcs /\ q \in suspect[p] 
                           THEN timeout[p][q] + 1 
                           ELSE timeout[p][q] ] ] 
        /\ last' = [last EXCEPT ![p] = 
                     [last[p] EXCEPT ![q] = 
                        IF q \in recSrcs 
                        THEN 0 
                        ELSE IF last[p][q] < timeout[p][q] 
                             THEN last[p][q] + 1 
                             ELSE last[p][q] ] ] 
        /\ clock' = [clock EXCEPT ![p] = ClockInc(p)]
        /\ outbox' = outbox
        /\ UNCHANGED <<suspect, timeout, last, clock, outbox>>

\*--------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------

Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\*--------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------

Spec == Init /\ [][Next]_<<suspect, timeout, last, clock, outbox>>

====