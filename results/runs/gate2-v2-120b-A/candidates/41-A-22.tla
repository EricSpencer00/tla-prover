---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (instantiated by the .cfg file)
\* ----------------------------------------------------------------------
CONSTANTS 
    Proc,           \* Set of processes
    d0,             \* Default timeout interval (positive integer)
    SendPoint,      \* Positive integer send interval
    PredictPoint,   \* Positive integer predict interval
    Messages        \* Set of messages (supplied by the controller)

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Other(p) == Proc \ {p}

\* ----------------------------------------------------------------------
\* Message type definition
\* ----------------------------------------------------------------------
MsgAlive == [type : "alive", src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES 
    susp,       \* [p \in Proc -> SUBSET Proc]   (suspicion set of each process)
    to,         \* [p \in Proc -> [q \in Other(p) -> Nat]]   (timeout intervals)
    last,       \* [p \in Proc -> [q \in Other(p) -> Nat]]   (ticks since last alive)
    clk,        \* [p \in Proc -> Nat]        (local clock of each process)
    out         \* [p \in Proc -> SUBSET MsgAlive]   (outgoing messages)

\* ----------------------------------------------------------------------
\* State constraints (type invariant)
\* ----------------------------------------------------------------------
TypeOK ==
    /\ susp \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc: susp[p] \subseteq Other(p)
    /\ to \in [Proc -> [Other(p) -> Nat]]
    /\ last \in [Proc -> [Other(p) -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET MsgAlive]

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ susp = [p \in Proc |-> {}]
    /\ to   = [p \in Proc |-> [q \in Other(p) |-> d0]]
    /\ last = [p \in Proc |-> [q \in Other(p) |-> 0]]
    /\ clk  = [p \in Proc |-> 0]
    /\ out  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllOther(p) == Other(p)

\* Increment all last-heard counters for a process p (used in SendAlive and Predict)
IncLast(p) ==
    [last[p] EXCEPT ![q] = @ + 1 \* for all q \in Other(p)
    ]

\* Reset the last-heard counter for a specific sender q of process p
ResetLast(p, q) ==
    [last[p] EXCEPT ![q] = 0]

\* Reset the local clock of a process p to 0
ResetClk(p) ==
    [clk EXCEPT ![p] = 0]

\* ----------------------------------------------------------------------
\* Process actions
\* ----------------------------------------------------------------------
SendAlive(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0          \* ensure not simultaneous
    /\ out' = [out EXCEPT ![p] = 
                { [type |-> "alive", src |-> p, dst |-> q] : q \in Other(p) } ]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last' = IncLast(p)
    /\ UNCHANGED <<susp, to>>

Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0            \* ensure not simultaneous
    /\ susp' = [susp EXCEPT ![p] = 
                susp[p] \cup 
                { q \in Other(p) : last[p][q] >= to[p][q] }]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last' = IncLast(p)
    /\ UNCHANGED <<to, out>>

Receive(p) ==
    /\ ~ (clk[p] % SendPoint = 0 /\ clk[p] % PredictPoint # 0)
    /\ ~ (clk[p] % PredictPoint = 0 /\ clk[p] % SendPoint # 0)
    /\ \E msgs \in SUBSET Messages :
        /\ \A m \in msgs :
            /\ m.type = "alive"
            /\ m.dst = p
            /\ m.src \in Other(p)
        /\ \A s \in msgs :
            /\ out[s.src] = out[s.src] \ { [type |-> "alive", src |-> s.src, dst |-> p] }
        /\ out' = [out EXCEPT ![p] = {}]
        /\ \A m \in msgs :
            let src == m.src in
            /\ last' = [last EXCEPT ![p][src] = 0]
            /\ IF src \in susp[p]
               THEN to' = [to EXCEPT ![p][src] = to[p][src] + 1]
               ELSE to' = to
        /\ clk' = ResetClk(p)
        /\ UNCHANGED <<susp>>

\* ----------------------------------------------------------------------
\* Clock wrap‑around (reset when exceeding all relevant thresholds)
\* ----------------------------------------------------------------------
ClockWrap ==
    /\ \A p \in Proc :
        clk[p] > Max({SendPoint, PredictPoint} \cup 
                     { to[p][q] : q \in Other(p) })
    /\ clk' = ResetClk(Proc)   \* resets every clock to 0
    /\ UNCHANGED <<susp, to, last, out>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : SendAlive(p)
    \/ \E p \in Proc : Predict(p)
    \/ \E p \in Proc : Receive(p)
    \/ ClockWrap

\* ----------------------------------------------------------------------
\* Specification (required by the .cfg)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<<susp, to, last, clk, out>>

\* ----------------------------------------------------------------------
\* The INVARIANT required by the .cfg
\* ----------------------------------------------------------------------
INVARIANTS == TypeOK

====