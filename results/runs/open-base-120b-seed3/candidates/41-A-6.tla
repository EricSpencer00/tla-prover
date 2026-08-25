---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be supplied by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS
    Proc,        \* Set of process identifiers
    d0,          \* Default timeout interval (positive integer)
    SendPoint,   \* Send interval (positive integer)
    PredictPoint,\* Predict interval (positive integer)
    Messages     \* Set of possible messages (must be a subset of Message)

\* ----------------------------------------------------------------------
\* Message definition
\* ----------------------------------------------------------------------
Message == [type : {"alive"}, src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
OtherProc(p) == Proc \ {p}

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    sus,   \* suspicion sets: [p \in Proc |-> SUBSET Proc]
    tout,  \* timeout intervals: [p \in Proc |-> [q \in Proc |-> Nat]]
    last,  \* last‑heard counters: [p \in Proc |-> [q \in Proc |-> Nat]]
    clk,   \* local clocks: [p \in Proc |-> Nat]
    out    \* outgoing messages: [p \in Proc |-> SUBSET Messages]

vars == << sus, tout, last, clk, out >>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsMultiple(x, y) == \E k \in Nat : x = y * k

SendEnabled(p) == IsMultiple(clk[p], SendPoint) /\ ~IsMultiple(clk[p], PredictPoint)
PredictEnabled(p) == IsMultiple(clk[p], PredictPoint) /\ ~IsMultiple(clk[p], SendPoint)

\* All alive messages a process p would create
AliveMsgs(p) == { [type |-> "alive", src |-> p, dst |-> q] : q \in OtherProc(p) }

\* The set of all messages currently in transit (outgoing from any process)
AllMessages == UNION { out[r] : r \in Proc }

\* Incoming messages for a particular destination process
Incoming(p) == { m \in AllMessages : m.dst = p }

\* Sources of messages received by p in the current step
Sources(p) == { m.src : m \in Incoming(p) }

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ sus = [p \in Proc |-> {}]
    /\ tout = [p \in Proc |-> [q \in Proc |-> IF q # p THEN d0 ELSE 0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk = [p \in Proc |-> 0]
    /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send action (alive messages)
\* ----------------------------------------------------------------------
Send(p) ==
    /\ SendEnabled(p)
    /\ out' = [out EXCEPT ![p] = AliveMsgs(p)]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ \A q \in OtherProc(p) :
          last' = [last EXCEPT ![p][q] = IF last[p][q] < tout[p][q] THEN last[p][q] + 1 ELSE last[p][q]]
    /\ UNCHANGED << sus, tout >>
    /\ \A r \in Proc \ {p} : out'[r] = out[r]

\* ----------------------------------------------------------------------
\* Predict action (suspicion update)
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ PredictEnabled(p)
    /\ sus' = [sus EXCEPT ![p] = sus[p] \cup
               { q \in OtherProc(p) : last[p][q] > tout[p][q] }]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ \A q \in OtherProc(p) :
          last' = [last EXCEPT ![p][q] = last[p][q] + 1]
    /\ UNCHANGED << tout, out >>
    /\ \A r \in Proc \ {p} : out'[r] = out[r]

\* ----------------------------------------------------------------------
\* Receive action (process incoming messages)
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ ~SendEnabled(p) /\ ~PredictEnabled(p)
    /\ \* Reset last‑heard counters for sources from which a message is received
       last' = [last EXCEPT
                  ![p][src] = IF src \in Sources(p) THEN 0 ELSE last[p][src]
               ]
    /\ \* Remove sources from suspicion set (they are heard from)
       sus' = [sus EXCEPT ![p] = sus[p] \ Sources(p)]
    /\ \* Adaptive timeout increase for sources that were suspected
       tout' = [tout EXCEPT
                  ![p][src] = IF src \in Sources(p) /\ src \in sus[p] THEN tout[p][src] + 1
                               ELSE tout[p][src]
               ]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ out' = [out EXCEPT ![p] = {}]   \* after sending, the outgoing set is cleared
    /\ UNCHANGED << >>
    /\ \A r \in Proc \ {p} : out'[r] = out[r]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : sus[p] \subseteq OtherProc(p)
    /\ tout \in [Proc -> [Proc -> Nat]]
    /\ \A p \in Proc : \A q \in Proc :
          IF q # p THEN tout[p][q] \in Nat ELSE tout[p][q] = 0
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]
    /\ Messages \subseteq Message

\* ----------------------------------------------------------------------
\* Properties (placeholder – no liveness properties specified)
\* ----------------------------------------------------------------------
PROPERTIES == TRUE

====