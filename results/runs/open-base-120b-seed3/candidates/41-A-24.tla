---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* CONSTANTS (to be supplied by the configuration file)
\* ----------------------------------------------------------------------
CONSTANTS
    Proc,        \* Set of processes
    d0,          \* Default timeout interval (positive integer)
    SendPoint,   \* Send interval (positive integer)
    PredictPoint,\* Predict interval (positive integer)
    Messages     \* Set of possible messages

\* ----------------------------------------------------------------------
\* Types of messages used in the model
\* ----------------------------------------------------------------------
Message == [src : Proc, dst : Proc, type : {"alive"}]

\* ----------------------------------------------------------------------
\* VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    clock,       \* [p \in Proc |-> Nat]  local clock of each process
    suspicion,   \* [p \in Proc |-> SUBSET Proc]  set of processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  adaptive timeout intervals
    lastHeard,   \* [p \in Proc |-> [q \in Proc |-> Nat]]  ticks since p last heard from q
    msgs         \* SUBSET Messages  messages currently in the network

vars == <<clock, suspicion, timeout, lastHeard, msgs>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
\* Default timeout function (identical for all ordered pairs of distinct processes)
DefaultTimeout == [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]

\* Maximum relevant bound for a process's clock (send, predict, and all its timeouts)
MaxClock(p) ==
    LET T == { timeout[p][q] : q \in Proc \ {p} } \cup {SendPoint, PredictPoint}
    IN  CHOOSE x \in T : \A y \in T : y <= x

\* Increment a counter but keep it unchanged if it already exceeds its timeout
IncIfNotTimedOut(cnt, to) == IF cnt < to THEN cnt + 1 ELSE cnt

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = DefaultTimeout
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ msgs = {}

\* ----------------------------------------------------------------------
\* Per‑process actions
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ \* create alive messages for every other process
       let newMsgs == { [src |-> p, dst |-> q, type |-> "alive"] :
                         q \in Proc \ {p} } in
       msgs' = msgs \cup newMsgs
    /\ \* update local clock (wrap around if needed)
       clock' = [clock EXCEPT ![p] = 
                 IF clock[p] + 1 > MaxClock(p) THEN 0 ELSE clock[p] + 1]
    /\ \* update lastHeard counters for p
       lastHeard' = [lastHeard EXCEPT
                     ![p] = [lastHeard[p] EXCEPT
                               ![q] = IncIfNotTimedOut(lastHeard[p][q],
                                                       timeout[p][q])
                               \* for all q (including p) – the case q = p is irrelevant
                           | q \in Proc]]
    /\ UNCHANGED <<suspicion, timeout>>

Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ \* add to suspicion any process whose counter exceeds its timeout
       suspicion' = [suspicion EXCEPT 
                     ![p] = suspicion[p] \cup
                            { q \in Proc \ {p} :
                              lastHeard[p][q] > timeout[p][q] } ]
    /\ \* increment clock with wrap‑around
       clock' = [clock EXCEPT ![p] = 
                 IF clock[p] + 1 > MaxClock(p) THEN 0 ELSE clock[p] + 1]
    /\ \* update lastHeard counters for p (as in Send)
       lastHeard' = [lastHeard EXCEPT
                     ![p] = [lastHeard[p] EXCEPT
                               ![q] = IncIfNotTimedOut(lastHeard[p][q],
                                                       timeout[p][q])
                               | q \in Proc]]
    /\ UNCHANGED <<msgs, timeout>>

Receive(p) ==
    /\ \* any subset of alive messages addressed to p may be received
       LET rec == { m \in msgs :
                     /\ m.dst = p
                     /\ m.type = "alive"
                 } IN
       \* nondeterministically choose a subset of rec to actually be received
       \E r \subseteq rec :
         /\ msgs' = msgs \ rec \cup {}   \* remove the received messages
         /\ \* update lastHeard and suspicion for each sender q in r
            lastHeard' = [lastHeard EXCEPT
                          ![p] = [lastHeard[p] EXCEPT
                                    ![q] = IF q \in DOMAIN r THEN 0
                                            ELSE IncIfNotTimedOut(lastHeard[p][q],
                                                                 timeout[p][q])
                                    | q \in Proc]]
            /\ suspicion' = [suspicion EXCEPT
                             ![p] = suspicion[p] \ { q \in DOMAIN r } ]
            /\ timeout' = [timeout EXCEPT
                           ![p] = [timeout[p] EXCEPT
                                    ![q] = IF (q \in DOMAIN r) /\ (q \in suspicion[p])
                                            THEN timeout[p][q] + 1
                                            ELSE timeout[p][q]
                                    | q \in Proc]]
         /\ \* clock advances with wrap‑around
            clock' = [clock EXCEPT ![p] = 
                      IF clock[p] + 1 > MaxClock(p) THEN 0 ELSE clock[p] + 1]
    /\ UNCHANGED <<>>

\* ----------------------------------------------------------------------
\* Global next‑state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc : \/ Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ msgs \in SUBSET Messages
    /\ \A m \in msgs : 
          /\ m \in Message
          /\ m.src \in Proc
          /\ m.dst \in Proc
          /\ m.type = "alive"

\* ----------------------------------------------------------------------
\* Assumptions about constants
\* ----------------------------------------------------------------------
ASSUME SendPoint > 0
ASSUME PredictPoint > 0
ASSUME SendPoint % PredictPoint # 0
ASSUME PredictPoint % SendPoint # 0
ASSUME d0 > 0

\* ----------------------------------------------------------------------
\* The set of invariants and properties required by the .cfg file
\* ----------------------------------------------------------------------
INVARIANT TypeOK

====