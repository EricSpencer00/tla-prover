---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences

CONSTANTS
    Proc,          \* The set of processes
    d0,            \* Default timeout interval (positive integer)
    SendPoint,     \* Set of clock values at which a process sends alive messages
    PredictPoint,  \* Set of clock values at which a process makes predictions
    Messages       \* Set of all possible messages

\* ----------------------------------------------------------------------
\* State variables
VARIABLES
    sus,      \* Suspicion sets: [p \in Proc |-> SUBSET Proc]
    timeout,  \* Adaptive timeouts: [p \in Proc |-> [q \in Proc |-> Nat]]
    last,     \* Counters since last heard: [p \in Proc |-> [q \in Proc |-> Nat]]
    clk,      \* Local clocks: [p \in Proc |-> Nat]
    out       \* Outgoing messages: [p \in Proc |-> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Helper definition for an alive message
AliveMsg(p, q) == [type |-> "alive", from |-> p, to |-> q]

\* ----------------------------------------------------------------------
\* Initial state
Init ==
    /\ clk = [p \in Proc |-> 0]
    /\ sus = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Increment of a process' local clock (simple +1; reset omitted for brevity)
NextClock(p) ==
    clk[p] + 1

\* ----------------------------------------------------------------------
\* SEND action for a process p
Send(p) ==
    /\ clk[p] \in SendPoint
    /\ clk[p] \notin PredictPoint
    /\ out' = [out EXCEPT ![p] = { AliveMsg(p, q) : q \in Proc \ {p} } ]
    /\ clk' = [clk EXCEPT ![p] = NextClock(p)]
    /\ sus' = sus
    /\ timeout' = timeout
    /\ last' = [last EXCEPT ![p] = 
                [q \in Proc |-> IF last[p][q] < timeout[p][q] 
                               THEN last[p][q] + 1 
                               ELSE last[p][q]]]
    /\ UNCHANGED << sus, timeout, out >> \* (sus, timeout unchanged, out already defined)

\* ----------------------------------------------------------------------
\* PREDICT action for a process p
Predict(p) ==
    /\ clk[p] \in PredictPoint
    /\ clk[p] \notin SendPoint
    /\ sus' = [sus EXCEPT ![p] = 
                sus[p] \cup { q \in Proc \ {p} : last[p][q] > timeout[p][q] }]
    /\ clk' = [clk EXCEPT ![p] = NextClock(p)]
    /\ last' = [last EXCEPT ![p] = 
                [q \in Proc |-> IF last[p][q] < timeout[p][q] 
                               THEN last[p][q] + 1 
                               ELSE last[p][q]]]
    /\ timeout' = timeout
    /\ out' = out
    /\ UNCHANGED << sus, out >>

\* ----------------------------------------------------------------------
\* RECEIVE action for a process p
\* recvSet is the (nondeterministic) set of processes from which p receives an alive message
Receive(p) ==
    /\ clk[p] \notin SendPoint
    /\ clk[p] \notin PredictPoint
    /\ \E recvSet \subseteq Proc \ {p} :
        /\ (* Update last‑heard counters *)
           LET newLast == [last EXCEPT ![p] = 
                             [q \in Proc |-> IF q \in recvSet 
                                            THEN 0 
                                            ELSE last[p][q] + 1]] 
        /\ (* Remove from suspicion any process from which a message was received *)
           newSus == [sus EXCEPT ![p] = sus[p] \ recvSet]
        /\ (* Adaptive timeout increase for suspected senders that manage to send a message *)
           newTimeout == [timeout EXCEPT ![p] = 
                             [q \in Proc |-> IF q \in recvSet /\ q \in sus[p] 
                                            THEN timeout[p][q] + 1 
                                            ELSE timeout[p][q]]]
        /\ last' = newLast
        /\ sus' = newSus
        /\ timeout' = newTimeout
        /\ clk' = [clk EXCEPT ![p] = NextClock(p)]
        /\ out' = out
        /\ UNCHANGED << sus, timeout, out >>
    /\ UNCHANGED << clk, out >>

\* ----------------------------------------------------------------------
\* One step of the system: a single process performs one of its actions
ProcessStep ==
    \E p \in Proc :
        ( Send(p) \/ Predict(p) \/ Receive(p) )

Next == ProcessStep

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
    /\ sus \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<sus, timeout, last, clk, out>>

\* ----------------------------------------------------------------------
\* The required identifiers
INIT == Init
NEXT == Next
INVARIANTS == TypeOK

====