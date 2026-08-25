---- MODULE EPFailureDetector ----
EXTENDS Naturals, FiniteSets, TLC

\*--------------------------------------------------------------------
\* Constants (to be supplied by the .cfg file)
\*--------------------------------------------------------------------
CONSTANTS 
    Proc,          \* Set of processes
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer, not a multiple of SendPoint)
    Messages       \* Set of all possible messages

\*--------------------------------------------------------------------
\* Types of messages used in the model
\*--------------------------------------------------------------------
Message == [type : {"Alive"}, from : Proc, to : Proc]

\* We require that every alive message that can be created is a member of
\* the constant set Messages.
ASSUME \A p,q \in Proc : p # q => Message!["Alive", p, q] \in Messages

\*--------------------------------------------------------------------
\* State variables
\*--------------------------------------------------------------------
VARIABLES 
    Suspects,   \* \in [Proc -> SUBSET Proc]   (processes each process suspects)
    Timeout,    \* \in [Proc -> [Proc -> Nat]] (adaptive timeout intervals)
    Lc,         \* \in [Proc -> [Proc -> Nat]] (last‑heard counters)
    Clock,      \* \in [Proc -> Nat]           (local clocks)
    Outgoing    \* \in [Proc -> SUBSET Messages] (messages to send)

vars == << Suspects, Timeout, Lc, Clock, Outgoing >>

\*--------------------------------------------------------------------
\* Helper definitions
\*--------------------------------------------------------------------
AliveMsg(p,q) == [type |-> "Alive", from |-> p, to |-> q]

AllOther(p) == Proc \ {p}

\*--------------------------------------------------------------------
\* Initial state
\*--------------------------------------------------------------------
Init ==
    /\ Suspects = [p \in Proc |-> {}]
    /\ Timeout  = [p \in Proc |-> [q \in Proc |-> IF p # q THEN d0 ELSE 0]]
    /\ Lc       = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ Clock    = [p \in Proc |-> 0]
    /\ Outgoing = [p \in Proc |-> {}]

\*--------------------------------------------------------------------
\* Send‑alive action
\*--------------------------------------------------------------------
Send(p) ==
    /\ Clock[p] % SendPoint = 0
    /\ Clock[p] % PredictPoint # 0
    /\ \* create an alive message for every other process
       Outgoing' = [Outgoing EXCEPT ![p] = { AliveMsg(p,q) : q \in AllOther(p) }]
    /\ \* increment the local clock
       Clock'    = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ \* increment last‑heard counters for processes not yet timed‑out
       Lc' = [Lc EXCEPT ![p][q] = 
                IF Lc[p][q] < Timeout[p][q] 
                THEN Lc[p][q] + 1 
                ELSE Lc[p][q] 
                \* (no change when already timed‑out) 
                \* q ranges over all other processes
                \* (the definition works also for q = p because Lc[p][p] = 0 and Timeout[p][p]=0)
            \* for all q \in Proc
            ]
    /\ UNCHANGED << Suspects, Timeout, Outgoing \ {p} >>

\*--------------------------------------------------------------------
\* Predict action
\*--------------------------------------------------------------------
Predict(p) ==
    /\ Clock[p] % PredictPoint = 0
    /\ Clock[p] % SendPoint # 0
    /\ \* add to suspicion set every process whose counter exceeds its timeout
       Suspects' = [Suspects EXCEPT ![p] = 
                       Suspects[p] \cup 
                       { q \in AllOther(p) : Lc[p][q] > Timeout[p][q] }]
    /\ \* increment all last‑heard counters
       Lc' = [Lc EXCEPT ![p][q] = Lc[p][q] + 1]
    /\ \* increment the local clock
       Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ UNCHANGED << Timeout, Outgoing, Outgoing \ {p} >>

\*--------------------------------------------------------------------
\* Receive action (any other clock value)
\*--------------------------------------------------------------------
Receive(p) ==
    /\ ~(Clock[p] % SendPoint = 0 /\ Clock[p] % PredictPoint # 0)
    /\ ~(Clock[p] % PredictPoint = 0 /\ Clock[p] % SendPoint # 0)
    /\ \* the set of alive messages that p receives this step
       \E recv \subseteq { AliveMsg(q,p) : q \in AllOther(p) } :
          /\ \* update last‑heard counters and suspicion set for each sender q
             Lc' = [Lc EXCEPT 
                     ![p][q] = IF AliveMsg(q,p) \in recv 
                               THEN 0 
                               ELSE Lc[p][q] + 1
                   ]
          /\ Suspects' = [Suspects EXCEPT 
                           ![p] = { r \in Suspects[p] : 
                                    \A m \in recv : m.from # r } 
                         ]
          /\ \* adaptive timeout increase when a suspected process's message is received
             Timeout' = [Timeout EXCEPT 
                          ![p][q] = IF (q \in Suspects[p]) /\ (AliveMsg(q,p) \in recv)
                                    THEN Timeout[p][q] + 1
                                    ELSE Timeout[p][q] 
                        ]
          /\ \* outgoing messages are unchanged
             Outgoing' = Outgoing
          /\ \* increment the local clock
             Clock' = [Clock EXCEPT ![p] = Clock[p] + 1]
    /\ UNCHANGED << Suspects, Timeout, Lc, Clock, Outgoing \ {p} >> \* (variables not updated above stay unchanged)

\*--------------------------------------------------------------------
\* Next-state relation
\*--------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\*--------------------------------------------------------------------
\* Specification
\*--------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\*--------------------------------------------------------------------
\* Type invariant
\*--------------------------------------------------------------------
TypeOK ==
    /\ Suspects \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : Suspects[p] \subseteq AllOther(p)
    /\ Timeout \in [Proc -> [Proc -> Nat]]
    /\ \A p,q \in Proc : 
          (p # q => Timeout[p][q] \in Nat) /\ (p = q => Timeout[p][q] = 0)
    /\ Lc \in [Proc -> [Proc -> Nat]]
    /\ Clock \in [Proc -> Nat]
    /\ Outgoing \in [Proc -> SUBSET Messages]

\*--------------------------------------------------------------------
\* Properties (placeholder – no explicit safety/liveness beyond TypeOK)
\*--------------------------------------------------------------------
Properties == TRUE

=============================================================================