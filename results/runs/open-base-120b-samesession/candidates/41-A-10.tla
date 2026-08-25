---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS Proc, d0, SendPoint, PredictPoint, Messages

VARIABLES clock, suspicion, timeout, last, out

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
IsSend(p) == 
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0

IsPredict(p) == 
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ clock = [p \in Proc |-> 0]
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ last = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ out = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send alive messages
\* ----------------------------------------------------------------------
Send(p) ==
    LET newMsgs == { [type |-> "alive", from |-> p, to |-> q] : q \in Proc \ {p} } IN
    /\ IsSend(p)
    /\ out' = [out EXCEPT ![p] = newMsgs]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last' = [last EXCEPT ![p] = 
                [last[p] EXCEPT ![q] = IF q # p THEN last[p][q] + 1 ELSE @ ] ]
    /\ UNCHANGED << suspicion, timeout >>

\* ----------------------------------------------------------------------
\* Make predictions (update suspicion set)
\* ----------------------------------------------------------------------
Predict(p) ==
    LET newSus == { q \in Proc \ {p} : last[p][q] > timeout[p][q] } IN
    /\ IsPredict(p)
    /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup newSus]
    /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
    /\ last' = [last EXCEPT ![p] = 
                [last[p] EXCEPT ![q] = IF q # p THEN last[p][q] + 1 ELSE @ ] ]
    /\ UNCHANGED << timeout, out >>

\* ----------------------------------------------------------------------
\* Receive incoming alive messages
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ ~IsSend(p) /\ ~IsPredict(p)
    /\ \E rec \subseteq { m \in Messages : m.to = p } :
          LET recFrom == { m.from : m \in rec } IN
          /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
          /\ last' = [last EXCEPT ![p] = 
                      [last[p] EXCEPT 
                         ![q] = IF q \in recFrom THEN 0
                               ELSE IF q # p THEN last[p][q] + 1
                               ELSE @ ] ]
          /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \ { q \in recFrom } ]
          /\ timeout' = [timeout EXCEPT ![p] = 
                         [timeout[p] EXCEPT 
                            ![q] = IF q \in recFrom /\ q \in suspicion[p] THEN timeout[p][q] + 1
                                  ELSE @ ] ]
          /\ out' = [out EXCEPT ![p] = {}]
          /\ UNCHANGED << >>

\* ----------------------------------------------------------------------
\* Next-state relation (interleaving semantics)
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc: Send(p)
    \/ \E p \in Proc: Predict(p)
    \/ \E p \in Proc: Receive(p)

\* ----------------------------------------------------------------------
\* State variables tuple
\* ----------------------------------------------------------------------
vars == << clock, suspicion, timeout, last, out >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ clock \in [Proc -> Nat]
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout \in [Proc -> [Proc -> Nat]]
    /\ last \in [Proc -> [Proc -> Nat]]
    /\ out \in [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Specification (optional, not required by the .cfg but useful)
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

====