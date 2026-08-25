---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES suspicion, timeout, lastHeard, clock, outgoing

\* ----------------------------------------------------------------------
\* Types
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outgoing  \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout   = [p \in Proc |-> [q \in Proc |-> IF q # p THEN d0 ELSE 0]]
    /\ lastHeard = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock     = [p \in Proc |-> 0]
    /\ outgoing  = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveMessage(p, q) == [type |-> "alive", src |-> p, dst |-> q]

\* ----------------------------------------------------------------------
\* Send action (alive messages)
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ outgoing' = [outgoing EXCEPT ![p] = { AliveMessage(p, q) : q \in Proc \ {p} }]
    /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p][q] = IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                   THEN lastHeard[p][q] + 1
                                   ELSE lastHeard[p][q] ]
    /\ UNCHANGED << suspicion, timeout >>

\* ----------------------------------------------------------------------
\* Predict action (update suspicion set)
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ suspicion' = [suspicion EXCEPT
                        ![p] = suspicion[p] \cup
                               { q \in Proc \ {p} : lastHeard[p][q] > timeout[p][q] } ]
    /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
    /\ lastHeard' = [lastHeard EXCEPT
                        ![p][q] = IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                   THEN lastHeard[p][q] + 1
                                   ELSE lastHeard[p][q] ]
    /\ UNCHANGED << timeout, outgoing >>

\* ----------------------------------------------------------------------
\* Receive action (process incoming alive messages)
\* ----------------------------------------------------------------------
Receive(p) ==
    \E rec \in SUBSET { m \in Messages : m.dst = p } :
        LET srcs == { m.src : m \in rec } IN
        /\ lastHeard' = [lastHeard EXCEPT
                            ![p][q] = IF q \in srcs
                                      THEN 0
                                      ELSE IF q # p /\ lastHeard[p][q] < timeout[p][q]
                                           THEN lastHeard[p][q] + 1
                                           ELSE lastHeard[p][q] ]
        /\ suspicion' = [suspicion EXCEPT
                            ![p] = suspicion[p] \ srcs ]
        /\ timeout'   = [timeout EXCEPT
                            ![p][q] = IF q \in srcs /\ q \in suspicion[p]
                                      THEN timeout[p][q] + 1
                                      ELSE timeout[p][q] ]
        /\ clock'     = [clock EXCEPT ![p] = clock[p] + 1]
        /\ outgoing'  = outgoing
        /\ UNCHANGED << suspicion, timeout, lastHeard, clock, outgoing >>

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
vars == << suspicion, timeout, lastHeard, clock, outgoing >>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariant required by the configuration
\* ----------------------------------------------------------------------
INVARIANT TypeOK

=============================================================================