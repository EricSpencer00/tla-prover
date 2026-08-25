---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive Nat)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of possible messages (must contain all alive messages)

VARIABLES
    sus,        \* [Proc -> SUBSET Proc]  suspicion sets per process
    timeout,    \* [Proc -> [Proc -> Nat]] adaptive timeout intervals per process pair
    last,       \* [Proc -> [Proc -> Nat]] counters since last heard
    clk,        \* [Proc -> Nat]          local clocks
    out         \* [Proc -> SUBSET Messages] outgoing messages per process

\* -------------------------------------------------------------------------
\* Helper definitions
\* -------------------------------------------------------------------------

AliveMsg(p, q) == 
    [type |-> "alive", src |-> p, dst |-> q]

SendSet(p) == 
    { AliveMsg(p, q) : q \in Proc \ {p} }

IncLast(last) ==
    [p \in Proc |-> [q \in Proc |-> last[p][q] + 1]]

NextClock(p) ==
    LET maxT == Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Proc \ {p} })
    IN IF clk[p] + 1 > maxT THEN 0 ELSE clk[p] + 1

\* -------------------------------------------------------------------------
\* Initial state
\* -------------------------------------------------------------------------

Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk = [p \in Proc |-> 0]
    /\ out = [p \in Proc |-> {}]

\* -------------------------------------------------------------------------
\* Actions
\* -------------------------------------------------------------------------

Send(p) ==
    /\ (clk[p] % SendPoint) = 0
    /\ (clk[p] % PredictPoint) # 0
    /\ out' = [out EXCEPT ![p] = SendSet(p)]
    /\ sus' = sus
    /\ timeout' = timeout
    /\ last' = IncLast(last)
    /\ clk' = [clk EXCEPT ![p] = NextClock(p)]

Predict(p) ==
    /\ (clk[p] % PredictPoint) = 0
    /\ (clk[p] % SendPoint) # 0
    /\ sus' = [sus EXCEPT ![p] = sus[p] \cup { q \in Proc : last[p][q] > timeout[p][q] }]
    /\ out' = out
    /\ timeout' = timeout
    /\ last' = IncLast(last)
    /\ clk' = [clk EXCEPT ![p] = NextClock(p)]

Receive(p) ==
    /\ (clk[p] % SendPoint) # 0
    /\ (clk[p] % PredictPoint) # 0
    /\ \E incSet \subseteq { m \in Messages : m.dst = p } :
        LET resetSet == { m.src : m \in incSet } IN
        /\ sus' = [sus EXCEPT ![p] = sus[p] \ setdiff resetSet]
        /\ timeout' = [timeout EXCEPT 
                         ![p] = [timeout[p] EXCEPT 
                                   ![q] = IF q \in resetSet /\ q \in sus[p] 
                                          THEN timeout[p][q] + 1 
                                          ELSE timeout[p][q] ] ]
        /\ last' = [last EXCEPT 
                      ![p] = [last[p] EXCEPT 
                                ![q] = IF q \in resetSet THEN 0 ELSE last[p][q] + 1 ] ]
        /\ out' = out
        /\ clk' = [clk EXCEPT ![p] = NextClock(p)]

Next ==
    \/ \E p \in Proc : Send(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)

\* -------------------------------------------------------------------------
\* Specification
\* -------------------------------------------------------------------------

Spec == Init /\ [][Next]_<<sus, timeout, last, clk, out>>

\* -------------------------------------------------------------------------
\* Type invariant
\* -------------------------------------------------------------------------

TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]

\* -------------------------------------------------------------------------
\* Theorems / Properties (placeholder for future liveness)
\* -------------------------------------------------------------------------

====