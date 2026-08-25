---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* Message definition (must be a subset of the constant Messages)
Message == [type : {"alive"}, from : Proc, to : Proc]

\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]   -- processes p suspects
    timeout,     \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- timeout intervals
    last,        \* [p \in Proc |-> [q \in Proc |-> Nat]]  -- ticks since last alive
    clk,         \* [p \in Proc |-> Nat]         -- local clocks
    out          \* [p \in Proc |-> SUBSET Messages]  -- outgoing messages

\* ----------------------------------------------------------------------
\* Helper definitions
\* All processes other than p
Other(p) == Proc \ {p}

\* Maximum of a non‑empty finite set of naturals
Max(S) == IF S = {} THEN 0 ELSE
          CHOOSE x \in S : \A y \in S : x >= y

\* Upper bound for a process's clock
ClockBound(p) ==
    Max({SendPoint, PredictPoint} \cup { timeout[p][q] : q \in Other(p) })

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last      = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE 0]]
    /\ clk       = [p \in Proc |-> 0]
    /\ out       = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send‑alive action for a process p
Send(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { [type |-> "alive", from |-> p, to |-> q] :
                                   q \in Other(p) }]
    /\ suspicion' = suspicion
    /\ timeout'   = timeout
    /\ clk' = [clk EXCEPT ![p] = 
               IF clk[p] + 1 > ClockBound(p) THEN 0 ELSE clk[p] + 1]
    /\ last' = [last EXCEPT ![p][q] = @ + 1 
                \* increment for all q ≠ p
                \* (if a timeout already expired we still increment;
                \* the prediction step will handle suspicion)
                \* Note: q = p entries are irrelevant
                \* and remain 0
                \* (the EXCEPT syntax updates all q in Other(p))
                \* using a lambda for brevity
                \* The following is equivalent to a map over Other(p)
                \* but TLC permits the shorthand below.
                \* We keep the original value for q = p.
                ]
                ]

\* ----------------------------------------------------------------------
\* Predict action for a process p
Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ let newSuspects == { q \in Other(p) : last[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSuspects]
    /\ timeout'   = timeout
    /\ clk' = [clk EXCEPT ![p] = 
               IF clk[p] + 1 > ClockBound(p) THEN 0 ELSE clk[p] + 1]
    /\ out' = out
    /\ last' = [last EXCEPT ![p][q] = @ + 1 
                \* increment all counters (including those just suspected)
                ]

\* ----------------------------------------------------------------------
\* Receive action for a process p
Receive(p) ==
    /\ \* any subset of incoming alive messages may be received
       let recv == { m \in Messages :
                       /\ m.type = "alive"
                       /\ m.to   = p } in
       \* nondeterministically choose a subset
       \E R \subseteq recv :
         /\ LET senders == { m.from : m \in R } IN
            /\* Update last‑heard counters
               Reset to 0 for senders, increment otherwise
               /\ last' = [last EXCEPT
                     ![p][s] = IF s \in senders THEN 0 ELSE @ + 1
                     ]
            /\* Update suspicion set: remove any sender that is heard from
               /\ suspicion' = [suspicion EXCEPT
                     ![p] = suspicion[p] \ senders
                     ]
            /\* Adaptive timeout increase for senders that were previously suspected
               /\ timeout' = [timeout EXCEPT
                     ![p][s] = IF s \in senders /\ s \in suspicion[p]
                                 THEN @ + 1
                                 ELSE @
                     ]
            /\* Clock increment with wrap‑around
               /\ clk' = [clk EXCEPT ![p] =
                     IF clk[p] + 1 > ClockBound(p) THEN 0 ELSE clk[p] + 1]
            /\* Outgoing messages unchanged
               /\ out' = out
         ]

\* ----------------------------------------------------------------------
\* Next-state relation (any process takes one of the three actions)
Next ==
    \E p \in Proc : Send(p) \/ Predict(p) \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
Spec ==
    Init /\ [][Next]_<<suspicion, timeout, last, clk, out>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : suspicion[p] \subseteq Other(p)
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ \A p \in Proc : \A q \in Proc :
          (q = p) => timeout[p][q] = 0
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]
    /\ \A m \in Messages : m \in Message

\* ----------------------------------------------------------------------
\* (Optional) Property placeholder required by the task description
Properties == TRUE

=============================================================================