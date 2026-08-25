---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout value (positive integer)
    SendPoint,     \* Send interval (positive integer)
    PredictPoint,  \* Predict interval (positive integer)
    Messages       \* Set of possible messages (must contain all alive messages)

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Alive(p, q) == [type |-> "Alive", src |-> p, dst |-> q]

AllAliveMessages == { Alive(p, q) : p \in Proc, q \in Proc \ {p} }

\* Assume the environment supplies all alive messages in the message set
ASSUME AllAliveMessages \subseteq Messages

\* ----------------------------------------------------------------------
\* State variables
\* ----------------------------------------------------------------------
VARIABLES
    suspicion,   \* [p \in Proc |-> SUBSET Proc]  (process p's suspicion set)
    timeout,     \* [p \in Proc |-> [q \in Proc \ {p} |-> Nat]] (adaptive timeout)
    lastHeard,   \* [p \in Proc |-> [q \in Proc \ {p} |-> Nat]] (ticks since last alive)
    clk,         \* [p \in Proc |-> Nat] (local clock)
    out          \* [p \in Proc |-> SUBSET Messages] (outgoing messages)

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc \ {p} |-> d0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc \ {p} |-> 0]]
    /\ clk       = [p \in Proc |-> 0]
    /\ out       = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : suspicion[p] \subseteq Proc \ {p}
    /\ timeout \in [Proc -> [Proc \ {<<>>} -> Nat]]   \* each entry is a Nat
    /\ \A p \in Proc : timeout[p] \in [Proc \ {p} -> Nat]
    /\ lastHeard \in [Proc -> [Proc \ {<<>>} -> Nat]]
    /\ \A p \in Proc : lastHeard[p] \in [Proc \ {p} -> Nat]
    /\ clk \in [Proc -> Nat]
    /\ out \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Auxiliary definitions for clock handling
\* ----------------------------------------------------------------------
MaxTimeout ==
    LET vals == { timeout[p][q] : p \in Proc, q \in Proc \ {p} } IN
    IF vals = {} THEN 0 ELSE Max(vals)

MaxClock ==
    Max({SendPoint, PredictPoint, MaxTimeout})

\* ----------------------------------------------------------------------
\* Action: Send alive messages
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clk[p] % SendPoint = 0
    /\ clk[p] % PredictPoint # 0
    /\ out' = [out EXCEPT ![p] = { Alive(p, q) : q \in Proc \ {p} } ]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ suspicion' = suspicion
    /\ timeout'   = timeout
    /\ lastHeard' = [lastHeard EXCEPT
                       ![p][q] = IF q \notin suspicion[p] THEN lastHeard[p][q] + 1
                                ELSE lastHeard[p][q] ]
    /\ UNCHANGED << suspicion, timeout, lastHeard, clk, out >> \* will be overridden above

\* ----------------------------------------------------------------------
\* Action: Make predictions (suspicion)
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ clk[p] % PredictPoint = 0
    /\ clk[p] % SendPoint # 0
    /\ let newSuspects == { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } in
       suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSuspects]
    /\ clk' = [clk EXCEPT ![p] = clk[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT ![p][q] = lastHeard[p][q] + 1
                                            \* increment for all q
                     ]
    /\ timeout' = timeout
    /\ out' = out
    /\ UNCHANGED << suspicion, timeout, lastHeard, clk, out >> \* overridden above

\* ----------------------------------------------------------------------
\* Action: Receive messages (nondeterministic set of incoming alive msgs)
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ (* This action applies when the clock is not at a send or predict point *)
       (clk[p] % SendPoint # 0) /\ (clk[p] % PredictPoint # 0)
    /\ (* Nondeterministically choose any subset of alive messages addressed to p *)
       recv \in SUBSET { m \in Messages : m.type = "Alive" /\ m.dst = p }
    /\ (* Update suspicion, timeout, lastHeard according to received messages *)
       suspicion' = [suspicion EXCEPT
                       ![p] = suspicion[p] \ 
                              { src | \E m \in recv : m.src = src } ]
    /\ timeout' = [timeout EXCEPT
                     ![p][src] = IF src \in suspicion[p] /\ 
                                   (\E m \in recv : m.src = src)
                                 THEN timeout[p][src] + 1
                                 ELSE timeout[p][src] ]
    /\ lastHeard' = [lastHeard EXCEPT
                       ![p][q] = IF \E m \in recv : m.src = q
                                 THEN 0
                                 ELSE lastHeard[p][q] + 1 ]
    /\ clk' = [clk EXCEPT ![p] = 
                IF clk[p] + 1 > MaxClock
                THEN 0
                ELSE clk[p] + 1]
    /\ out' = out
    /\ UNCHANGED << suspicion, timeout, lastHeard, clk, out >> \* overridden above

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving of actions of a single process)
\* ----------------------------------------------------------------------
Next ==
    \E p \in Proc :
        \/ Send(p)
        \/ Predict(p)
        \/ Receive(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == << suspicion, timeout, lastHeard, clk, out >>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* The required identifiers for the .cfg file
\* ----------------------------------------------------------------------
INIT == Init
NEXT == Next
INVARIANT == TypeOK

====