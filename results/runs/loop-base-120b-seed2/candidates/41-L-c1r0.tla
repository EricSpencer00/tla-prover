---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants (to be supplied by the configuration)
\* ----------------------------------------------------------------------
CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive Nat)
    SendPoint,     \* Positive integer: send interval
    PredictPoint,  \* Positive integer: predict interval (not a multiple of SendPoint)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   -- processes p currently suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- adaptive timeout for each pair
    last,        \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since p last heard from q
    clk,         \* [p \in Proc |-> Nat]                   -- local clock of each process
    out          \* [p \in Proc |-> SUBSET Messages]      -- messages p intends to send

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
vars == <<suspicion, timeout, last, clk, out>>

\* A message record used by this specification
Message(src, dst, typ) == [src |-> src, dst |-> dst, type |-> typ]

\* The set of alive messages that process p would generate
AliveMsgs(p) == { Message(p, q, "alive") : q \in Proc \ {p} }

\* Whether the clock of p is at a send point (and not at a predict point)
SendCond(p) == (clk[p] % SendPoint = 0) /\ (clk[p] % PredictPoint # 0)

\* Whether the clock of p is at a predict point (and not at a send point)
PredictCond(p) == (clk[p] % PredictPoint = 0) /\ (clk[p] % SendPoint # 0)

\* The maximum relevant threshold for resetting the clock of p
MaxThreshold(p) ==
    LET timeoutVals == { timeout[p][q] : q \in Proc \ {p} } IN
    Max({SendPoint, PredictPoint} \cup timeoutVals)

\* Increment the local clock of p, resetting to 0 when it exceeds MaxThreshold(p)
IncClock(p, c) ==
    IF c + 1 > MaxThreshold(p) THEN 0 ELSE c + 1

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last      = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clk       = [p \in Proc |-> 0]
    /\ out       = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
Send(p) ==
    /\ SendCond(p)
    /\ out' = [out EXCEPT ![p] = AliveMsgs(p)]
    /\ clk' = [clk EXCEPT ![p] = IncClock(p, clk[p])]
    /\ last' = [last EXCEPT ![p][q] = 
                IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                ELSE last[p][q] ]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ PredictCond(p)
    /\ suspicion' = [suspicion EXCEPT ![p] = 
          suspicion[p] \cup { q \in Proc \ {p} : last[p][q] > timeout[p][q] } ]
    /\ clk' = [clk EXCEPT ![p] = IncClock(p, clk[p])]
    /\ last' = [last EXCEPT ![p][q] = 
                IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                ELSE last[p][q] ]
    /\ UNCHANGED <<timeout, out>>

Receive(p) ==
    /\ ~SendCond(p)
    /\ ~PredictCond(p)
    \* Gather all alive messages addressed to p that are currently in any outbox
    LET incoming == { m \in UNION { out[r] : r \in Proc } : m.dst = p } IN
    /\ clk' = [clk EXCEPT ![p] = IncClock(p, clk[p])]
    /\ last' =
        [last EXCEPT ![p][q] =
            IF \E m \in incoming : m.src = q
               THEN 0
               ELSE IF last[p][q] < timeout[p][q] THEN last[p][q] + 1
                    ELSE last[p][q] ]
    /\ suspicion' =
        [suspicion EXCEPT ![p] = suspicion[p] \ { q \in Proc : \E m \in incoming : m.src = q } ]
    /\ timeout' =
        [timeout EXCEPT ![p][q] =
            IF (q \in suspicion[p]) /\ (\E m \in incoming : m.src = q)
               THEN timeout[p][q] + 1
               ELSE timeout[p][q] ]
    /\ out' = out   \* outgoing messages are unchanged by a receive step

\* One step of the system: an arbitrary process performs one of its enabled actions
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
SPECIFICATION == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ last      \in [Proc -> [Proc -> Nat]]
    /\ clk       \in [Proc -> Nat]
    /\ out       \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc :
          suspicion[p] \subseteq Proc \ {p}
          /\ \A q \in Proc :
                (q = p) => timeout[p][q] = 0
                /\ (q # p) => timeout[p][q] >= 1

\* ----------------------------------------------------------------------
\* Additional required identifiers
\* ----------------------------------------------------------------------
Init == Init          \* alias to satisfy the required name
Next == Next          \* alias
INVARIANTS == TypeOK
PROPERTIES == TRUE    \* no explicit liveness properties required
====