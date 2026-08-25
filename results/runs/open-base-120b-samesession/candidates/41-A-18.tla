---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS 
    Proc,          \* Set of processes
    d0,            \* Default timeout value (Nat)
    SendPoint,     \* Positive integer: send interval
    PredictPoint, \* Positive integer: predict interval
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
VARIABLES 
    clk,    \* [p \in Proc -> Nat]  local clock of each process
    sus,    \* [p \in Proc -> SUBSET Proc]  suspicion set of each process
    timeout,\* [p \in Proc -> [Proc -> Nat]]  adaptive timeout per destination
    last,   \* [p \in Proc -> [Proc -> Nat]]  ticks since last alive from each process
    out     \* [p \in Proc -> SUBSET Messages]  outgoing messages ready to be sent

\* ----------------------------------------------------------------------
\* Helper definitions
\* Max threshold used for (optional) clock reset – not required for safety
MaxThresh(p) == 
    Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc \ {p} })

NewClock(p) == 
    LET c == clk[p] + 1 IN 
    IF c > MaxThresh(p) THEN 0 ELSE c

\* ----------------------------------------------------------------------
\* Initialization
Init == 
    /\ clk = [p \in Proc |-> 0]
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* SendAlive action
SendAlive(p) == 
    /\ p \in Proc
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0                \* not a predict step
    /\ out' = [out EXCEPT ![p] = 
                { [type |-> "Alive", src |-> p, dst |-> q] : q \in Proc \ {p} } ]
    /\ clk' = [clk EXCEPT ![p] = NewClock(p)]
    /\ last' = [last EXCEPT ![p] = 
                [i \in Proc |-> 
                    IF i # p /\ last[p][i] < timeout[p][i] 
                    THEN last[p][i] + 1 
                    ELSE last[p][i] ]]
    /\ sus' = sus
    /\ timeout' = timeout
    /\ UNCHANGED << >> 

\* ----------------------------------------------------------------------
\* Predict action
Predict(p) == 
    /\ p \in Proc
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0                  \* not a send step
    /\ sus' = [sus EXCEPT ![p] = 
                sus[p] \cup { q \in Proc \ {p} : last[p][q] > timeout[p][q] } ]
    /\ clk' = [clk EXCEPT ![p] = NewClock(p)]
    /\ last' = [last EXCEPT ![p] = 
                [i \in Proc |-> IF i # p THEN last[p][i] + 1 ELSE last[p][i] ]]
    /\ out' = out
    /\ timeout' = timeout
    /\ UNCHANGED << >> 

\* ----------------------------------------------------------------------
\* Receive action (any step that is neither Send nor Predict)
Receive(p) == 
    /\ p \in Proc
    /\ clk[p] % SendPoint # 0
    /\ clk[p] % PredictPoint # 0
    /\ \E R \subseteq Proc \ {p} : 
       /\ (* R is the set of sources from which p receives an alive message this step *)
       /\ clk' = [clk EXCEPT ![p] = NewClock(p)]
       /\ out' = out
       /\ sus' = [sus EXCEPT ![p] = sus[p] \ R]
       /\ timeout' = [timeout EXCEPT ![p] = 
                      [i \in Proc |-> 
                         IF i \in R /\ i \in sus[p] 
                         THEN timeout[p][i] + 1 
                         ELSE timeout[p][i] ]]
       /\ last' = [last EXCEPT ![p] = 
                   [i \in Proc |-> 
                      IF i \in R 
                      THEN 0 
                      ELSE IF i # p 
                           THEN last[p][i] + 1 
                           ELSE last[p][i] ]]
       /\ UNCHANGED << >> 

\* ----------------------------------------------------------------------
\* Next-state relation
Next == 
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK == 
    /\ \A p \in Proc :
        /\ clk[p] \in Nat
        /\ sus[p] \subseteq Proc \ {p}
        /\ timeout[p] \in [Proc -> Nat]
        /\ last[p] \in [Proc -> Nat]
        /\ out[p] \subseteq Messages

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<clk, sus, timeout, last, out>>

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
INIT == Init
NEXT == Next
INVARIANTS == TypeOK

====