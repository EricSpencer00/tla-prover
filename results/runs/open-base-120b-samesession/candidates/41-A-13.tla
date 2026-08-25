---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

\*=====================================================================
\* Constants (to be supplied by the configuration)
\*=====================================================================
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible messages

\*=====================================================================
\* State variables
\*=====================================================================
VARIABLES
    sus,      \* [p \in Proc -> SUBSET Proc]  : suspicion set of each process
    timeout,  \* [p \in Proc -> [q \in Proc -> Nat]] : adaptive timeout intervals
    last,     \* [p \in Proc -> [q \in Proc -> Nat]] : ticks since last alive received
    clk,      \* [p \in Proc -> Nat]                 : local clock per process
    out       \* [p \in Proc -> SUBSET Messages]    : outgoing messages to be sent

\*=====================================================================
\* Helper definitions
\*=====================================================================
AllNotTimedOut(p) == { q \in Proc : last[p][q] < timeout[p][q] }

IncCounters(l, p) == 
    [ q \in Proc |-> 
        IF q \in AllNotTimedOut(p) 
            THEN l[p][q] + 1 
            ELSE l[p][q] ]

ResetClock(c, p) == 
    LET maxTimeout == 
            Max( { SendPoint, PredictPoint } \cup { timeout[p][q] : q \in Proc } )
    IN IF c > maxTimeout THEN 0 ELSE c

AliveMessage(p, q) == [type |-> "alive", src |-> p, dst |-> q]

AliveMessagesFrom(p) == { AliveMessage(p, q) : q \in Proc \ {p} }

\*=====================================================================
\* Initialization
\*=====================================================================
Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk = [p \in Proc |-> 0]
    /\ out = [p \in Proc |-> {}]

\*=====================================================================
\* Process actions
\*=====================================================================
Send(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0               \* send and predict never coincide
    /\ out' = [out EXCEPT ![p] = AliveMessagesFrom(p)]
    /\ sus' = sus
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p] = IncCounters(last, p)]
    /\ clk' = [clk EXCEPT ![p] = ResetClock(clk[p] + 1, p)]
    /\ UNCHANGED << sus, timeout, last, clk, out >> \* other processes unchanged

Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ sus' = [sus EXCEPT ![p] = 
                sus[p] \cup { q \in Proc \ {p} : last[p][q] > timeout[p][q] } ]
    /\ out' = out
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p] = IncCounters(last, p)]
    /\ clk' = [clk EXCEPT ![p] = ResetClock(clk[p] + 1, p)]
    /\ UNCHANGED << sus, timeout, last, clk, out >> \* other processes unchanged

Receive(p) ==
    /\ \* this action applies when neither send nor predict fires
       /\ ~(clk[p] % SendPoint = 0 /\ clk[p] % PredictPoint # 0)
       /\ ~(clk[p] % PredictPoint = 0 /\ clk[p] % SendPoint # 0)
    /\ \* nondeterministically assume any subset of alive messages addressed to p
       \* arrives in this step; we model their effect directly.
    /\ \* For each q \in Proc, define whether an alive from q is received:
       \*   recv_q ∈ {TRUE, FALSE}
    /\ \E recv \in [Proc -> BOOLEAN] :
          /\ \* Update last and suspicion according to received messages
          /\ last' = [ last EXCEPT ![p] = 
                [ q \in Proc |-> 
                    IF recv[q] 
                        THEN 0 
                        ELSE IF q \in AllNotTimedOut(p) 
                                THEN last[p][q] + 1 
                                ELSE last[p][q] ] ]
          /\ sus' = [ sus EXCEPT ![p] = 
                { q \in sus[p] : ~recv[q] } ]
          /\ timeout' = [ timeout EXCEPT ![p] = 
                [ q \in Proc |-> 
                    IF recv[q] /\ q \in sus[p] 
                        THEN timeout[p][q] + 1 
                        ELSE timeout[p][q] ] ]
          /\ out' = out
          /\ clk' = [clk EXCEPT ![p] = ResetClock(clk[p] + 1, p)]
          /\ UNCHANGED << sus, timeout, last, clk, out >> \* other processes unchanged
    /\ TRUE   \* (the existence of such recv is guaranteed)

\*=====================================================================
\* Next-state relation (interleaving of single‑process steps)
\*=====================================================================
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\*=====================================================================
\* Type invariant
\*=====================================================================
TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc : \A q \in Proc :
          (timeout[p][q] >= d0) /\ (last[p][q] >= 0)

\*=====================================================================
\* Specification
\*=====================================================================
Spec == Init /\ [][Next]_<<sus, timeout, last, clk, out>>

\*=====================================================================
\* The required identifiers
\*=====================================================================
INIT Init
INVARIANT TypeOK

====