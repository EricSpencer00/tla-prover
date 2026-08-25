---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS 
    Proc,          \* set of process identifiers
    d0,            \* default timeout interval (positive integer)
    SendPoint,     \* send interval (positive integer)
    PredictPoint,  \* predict interval (positive integer)
    Messages       \* set of all possible messages

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Message == [src : Proc, dst : Proc, type : {"alive"}]

\* A message is valid iff it belongs to the constant set Messages
IsMessage(m) == m \in Messages

\* All messages used by the specification are of type "alive"
AliveMessage(p, q) == [src |-> p, dst |-> q, type |-> "alive"]

\* Compute the next clock value, resetting to 0 when it exceeds all
\* relevant thresholds (send interval, predict interval, and all timeouts).
NextClock(p, clk, to) ==
    LET nxt == clk + 1 IN
    IF /\ nxt > SendPoint
       /\ nxt > PredictPoint
       /\ \A q \in Proc : nxt > to[p][q]
    THEN 0
    ELSE nxt

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES 
    suspicion,   \* [p \in Proc |-> SUBSET Proc]
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]
    counter,     \* [p \in Proc |-> [q \in Proc |-> Nat]]
    clock,       \* [p \in Proc |-> Nat]
    out,         \* [p \in Proc |-> SUBSET Messages]  (outgoing messages)
    net          \* SUBSET Messages  (messages in transit)

vars == <<suspicion, timeout, counter, clock, out, net>>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> d0]]
    /\ counter   = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ out       = [p \in Proc |-> {}]
    /\ net       = {}

\* ----------------------------------------------------------------------
\* Actions for a single process p
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ \* create alive messages for every other process
       msgs == { AliveMessage(p, q) : q \in Proc \ {p} }
    /\ out'   = [out EXCEPT ![p] = msgs]
    /\ net'   = net \cup msgs
    /\ counter' = [counter EXCEPT ![p][q] = 
                     IF counter[p][q] < timeout[p][q] 
                     THEN counter[p][q] + 1 
                     ELSE counter[p][q] 
                 FOR q \in Proc]
    /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p], timeout)]
    /\ suspicion' = suspicion
    /\ timeout'   = timeout

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ newSusps == { q \in Proc \ {p} : counter[p][q] > timeout[p][q] }
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSusps]
    /\ timeout'   = timeout
    /\ out'       = out
    /\ net'       = net
    /\ counter' = [counter EXCEPT ![p][q] = 
                     IF counter[p][q] < timeout[p][q] 
                     THEN counter[p][q] + 1 
                     ELSE counter[p][q] 
                 FOR q \in Proc]
    /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p], timeout)]

Receive(p) ==
    /\ \* not a send step and not a predict step
       /\ ~(clock[p] % SendPoint = 0 /\ clock[p] % PredictPoint # 0)
       /\ ~(clock[p] % PredictPoint = 0 /\ clock[p] % SendPoint # 0)
    /\ \E msgs \subseteq { m \in net : m.dst = p /\ m.type = "alive" } :
        /\ \* messages actually received in this step
           let senders == { m.src : m \in msgs } in
           /\ out' = out
           /\ net' = net \ msgs
           /\ \* reset counters for senders, otherwise increment (if not timed out)
              counter' = [counter EXCEPT ![p][q] = 
                            IF q \in senders 
                            THEN 0
                            ELSE IF counter[p][q] < timeout[p][q] 
                                 THEN counter[p][q] + 1
                                 ELSE counter[p][q]
                         FOR q \in Proc]
           /\ \* remove senders from suspicion set
              suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ senders]
           /\ \* adaptive timeout increase for suspected senders whose messages arrived
              timeout' = [timeout EXCEPT ![p][q] = 
                            IF q \in senders /\ q \in suspicion[p] 
                            THEN timeout[p][q] + 1 
                            ELSE timeout[p][q]
                         FOR q \in Proc]
           /\ clock' = [clock EXCEPT ![p] = NextClock(p, clock[p], timeout)]

\* ----------------------------------------------------------------------
\* Next-state relation (any process may take a step)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ counter   \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ out       \in [Proc -> SUBSET Messages]
    /\ net       \in SUBSET Messages
    /\ \A m \in out[p] : IsMessage(m)
    /\ \A m \in net    : IsMessage(m)

\* ----------------------------------------------------------------------
\* Assumptions about constants
\* ----------------------------------------------------------------------
ASSUME
    /\ SendPoint > 0
    /\ PredictPoint > 0
    /\ SendPoint % PredictPoint # 0
    /\ PredictPoint % SendPoint # 0
    /\ d0 > 0
    /\ Proc /= {}

\* ----------------------------------------------------------------------
\* Specification (optional, not required by the .cfg but useful)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* The identifiers required by the .cfg file
\* ----------------------------------------------------------------------
INIT Init
NEXT Next
INVARIANT TypeOK

====