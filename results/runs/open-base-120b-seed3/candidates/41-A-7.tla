---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive Nat)
    SendPoint,     \* Send interval (positive Nat)
    PredictPoint,  \* Predict interval (positive Nat)
    Messages       \* Set of possible messages

VARIABLES 
    clk,   \* [Proc -> Nat]   local clocks
    tout,  \* [Proc -> [Proc -> Nat]] timeout intervals
    last,  \* [Proc -> [Proc -> Nat]] counters since last heard
    sus,   \* [Proc -> SUBSET Proc] suspicion sets
    out    \* [Proc -> SUBSET Messages] outgoing messages

\*--------------------------------------------------------------
\* Helper definition: the maximal relevant clock value for a process
MaxClock(p) ==
    LET vals == {SendPoint, PredictPoint} \cup 
                { tout[p][q] : q \in Proc \ {p} } IN
    Max(vals)

\*--------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ clk \in [Proc -> Nat]
    /\ tout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ sus \in [Proc -> SUBSET Proc]
    /\ out \in [Proc -> SUBSET Messages]

\*--------------------------------------------------------------
\* Initial state
Init ==
    /\ clk = [p \in Proc |-> 0]
    /\ tout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ sus = [p \in Proc |-> {}]
    /\ out = [p \in Proc |-> {}]

\*--------------------------------------------------------------
\* Action: send alive messages
SendAlive(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ LET newMsgs == { [type |-> "alive", src |-> p, dst |-> q] :
                         q \in Proc \ {p} } IN
       out' = [out EXCEPT ![p] = out[p] \cup newMsgs]
    /\ clk' = [clk EXCEPT ![p] = 
                IF clk[p] + 1 >= MaxClock(p) THEN 0 ELSE clk[p] + 1]
    /\ last' = [last EXCEPT ![p] = 
                [q \in Proc |-> 
                    IF q = p THEN last[p][q]
                    ELSE IF last[p][q] < tout[p][q] THEN last[p][q] + 1
                    ELSE last[p][q]]]
    /\ sus' = sus
    /\ UNCHANGED tout

\*--------------------------------------------------------------
\* Action: make predictions (update suspicion set)
Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ LET addSus == { q \in Proc \ {p} : last[p][q] > tout[p][q] } IN
       sus' = [sus EXCEPT ![p] = sus[p] \cup addSus]
    /\ clk' = [clk EXCEPT ![p] = 
                IF clk[p] + 1 >= MaxClock(p) THEN 0 ELSE clk[p] + 1]
    /\ last' = [last EXCEPT ![p] = 
                [q \in Proc |-> last[p][q] + 1]]
    /\ out' = out
    /\ UNCHANGED tout

\*--------------------------------------------------------------
\* Action: receive incoming alive messages
Receive(p) ==
    /\ \E msgs \in SUBSET Messages :
         /\ \A m \in msgs : 
                /\ m.dst = p
                /\ m.src \in Proc \ {p}
         /\ 
         LET srcSet == { m.src : m \in msgs } IN
         /\ 
         \* Reset counters for senders, remove them from suspicion set
         last' = [last EXCEPT ![p] = 
                    [q \in Proc |-> IF q \in srcSet THEN 0 ELSE last[p][q] + 1]]
         /\ sus' = [sus EXCEPT ![p] = sus[p] \ srcSet]
         /\ 
         \* Adaptive timeout increase for any sender that was previously suspected
         tout' = [tout EXCEPT ![p] = 
                    [q \in Proc |-> IF q \in srcSet /\ q \in sus[p] THEN tout[p][q] + 1
                                   ELSE tout[p][q]]]
         /\ clk' = [clk EXCEPT ![p] = 
                    IF clk[p] + 1 >= MaxClock(p) THEN 0 ELSE clk[p] + 1]
         /\ out' = out
         /\ UNCHANGED << >> )   \* all other variables unchanged

\*--------------------------------------------------------------
\* Overall next-state relation
Next ==
    \E p \in Proc : SendAlive(p) \/ Predict(p) \/ Receive(p)

\*--------------------------------------------------------------
\* Specification
SPECIFICATION ==
    Init /\ [][Next]_<<clk, tout, last, sus, out>>

\*--------------------------------------------------------------
\* Invariants (as required by the .cfg file)
INVARIANTS == TypeOK

\*--------------------------------------------------------------
\* Additional properties placeholder (none specified)
PROPERTIES == TRUE

====