---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, Sequences

CONSTANTS
    Proc,            \* Set of all processes
    d0,              \* Default timeout interval (positive integer)
    SendPoint,       \* Positive send interval
    PredictPoint,    \* Positive predict interval (not a multiple of SendPoint)
    Messages         \* Set of possible messages (for type checking)

\* ----------------------------------------------------------------------
\* Type definitions
Message == [src : Proc, dst : Proc]

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    suspect,         \* [p \in Proc |-> SUBSET Proc]  -- suspicion set of each process
    timeout,         \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- timeout intervals
    last,            \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last heard
    clk,             \* [p \in Proc |-> Nat]  -- local clock
    out,             \* [p \in Proc |-> SUBSET Message]  -- outgoing messages
    in               \* [p \in Proc |-> SUBSET Message]  -- incoming messages (environment)

\* ----------------------------------------------------------------------
\* Helper definitions
AliveMsg(p) == { [src |-> p, dst |-> q] : q \in Proc \ {p} }

IncAllLast(p) ==
    [last EXCEPT ![p][q] = @ + 1 \* for all q \in Proc
                ]

ResetLast(p, q) ==
    [last EXCEPT ![p][q] = 0]

NoMsgFrom(p, q) ==
    q \in suspect[p]

AddSuspect(p, q) ==
    [suspect EXCEPT ![p] = suspect[p] \cup {q}]

RemSuspect(p, q) ==
    [suspect EXCEPT ![p] = suspect[p] \ {q}]

IncTimeout(p, q) ==
    [timeout EXCEPT ![p][q] = timeout[p][q] + 1]

ResetClkIfNeeded(p) ==
    IF clk[p] > Max( SendPoint, PredictPoint,
                    \E q \in Proc : timeout[p][q] ) THEN
        [clk EXCEPT ![p] = 0]
    ELSE
        [clk EXCEPT ![p] = @]

\* ----------------------------------------------------------------------
\* Initialization
Init ==
    /\ suspect = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ last    = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk     = [p \in Proc |-> 0]
    /\ out     = [p \in Proc |-> {}]
    /\ in      = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Process actions
SendAlive(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = AliveMsg(p)]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last' = [last EXCEPT ![p][q] = @ + 1
                         \* increment counters for all q
               ]
    /\ UNCHANGED <<suspect, timeout, in>>

Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ LET timedOut == { q \in Proc : q # p /\ last[p][q] > timeout[p][q] } IN
       suspect' = [suspect EXCEPT ![p] = suspect[p] \cup timedOut]
    /\ clk'     = [clk EXCEPT ![p] = clk[p] + 1]
    /\ last'    = [last EXCEPT ![p][q] = @ + 1 \* increment all counters
               ]
    /\ UNCHANGED <<timeout, out, in>>

Receive(p) ==
    /\ \E m \in in[p] : m.dst = p
    /\ LET src == m.src IN
       /\ out' = [out EXCEPT ![p] = {}]
       /\ IF src \in suspect[p] THEN
             timeout' = [timeout EXCEPT ![p][src] = timeout[p][src] + 1]
          ELSE
             timeout' = timeout
       /\ suspect' = [suspect EXCEPT ![p] = suspect[p] \ {src}]
       /\ last'    = [last EXCEPT ![p][src] = 0]
    /\ clk' = ResetClkIfNeeded(p)
    /\ in'  = [in EXCEPT ![p] = {}]
    /\ UNCHANGED <<out>>

Idle(p) ==
    /\ \A m \in in[p] : FALSE \* no incoming message
    /\ clk' = ResetClkIfNeeded(p)
    /\ UNCHANGED <<suspect, timeout, last, out, in>>

ProcStep(p) ==
    \/ SendAlive(p)
    \/ Predict(p)
    \/ Receive(p)
    \/ Idle(p)

\* ----------------------------------------------------------------------
\* Next-state relation
Next ==
    \E p \in Proc : ProcStep(p)

\* ----------------------------------------------------------------------
\* Safety invariant (type correctness)
TypeOK ==
    /\ suspect \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last    \in [Proc -> [Proc -> Nat]]
    /\ clk     \in [Proc -> Nat]
    /\ out     \in [Proc -> SUBSET Message]
    /\ in      \in [Proc -> SUBSET Message]

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<suspect, timeout, last, clk, out, in>>

=============================================================================