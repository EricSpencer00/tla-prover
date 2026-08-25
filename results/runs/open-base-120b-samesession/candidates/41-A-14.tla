---- MODULE EPFailureDetector ----
EXTENDS Naturals, Sequences, FiniteSets, TLC

CONSTANTS 
    Proc,          \* Set of process identifiers
    d0,            \* Default timeout interval (positive Nat)
    SendPoint,     \* Period of sending alive messages (positive Nat)
    PredictPoint,  \* Period of making predictions (positive Nat)
    Messages       \* Set of possible messages

VARIABLES 
    suspicion,     \* [Proc -> SUBSET Proc]
    timeout,       \* [Proc -> [Proc -> Nat]]
    lastHeard,    \* [Proc -> [Proc -> Nat]]
    clock,         \* [Proc -> Nat]
    outBox         \* [Proc -> SUBSET Messages]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AliveMessage(p, q) == 
    [ src |-> p,
      dst |-> q,
      kind |-> "alive" ]

AllOther(p) == Proc \ {p}

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ suspicion = [p \in Proc |-> {}]
    /\ timeout    = [p \in Proc |-> [q \in Proc |-> IF q = p THEN 0 ELSE d0]]
    /\ lastHeard  = [p \in Proc |-> [q \in Proc |-> 0]]
    /\ clock      = [p \in Proc |-> 0]
    /\ outBox     = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Send alive messages
\* ----------------------------------------------------------------------
Send(p) ==
    /\ clock[p] % SendPoint = 0
    /\ clock[p] % PredictPoint # 0
    /\ LET newMsgs == { AliveMessage(p, q) : q \in AllOther(p) } IN
       /\ outBox'   = [outBox EXCEPT ![p] = outBox[p] \cup newMsgs]
       /\ clock'    = [clock EXCEPT ![p] = clock[p] + 1]
       /\ lastHeard' = [lastHeard EXCEPT
                         ![p] = [ q \in Proc |-> 
                                   IF q \notin suspicion[p]
                                   THEN lastHeard[p][q] + 1
                                   ELSE lastHeard[p][q] ]]
       /\ UNCHANGED << suspicion, timeout >>

\* ----------------------------------------------------------------------
\* Make predictions (suspicion updates)
\* ----------------------------------------------------------------------
Predict(p) ==
    /\ clock[p] % PredictPoint = 0
    /\ clock[p] % SendPoint # 0
    /\ LET toSuspect == { q \in Proc : lastHeard[p][q] > timeout[p][q] } IN
       /\ suspicion' = [suspicion EXCEPT ![p] = suspicion[p] \cup toSuspect]
       /\ clock'     = [clock EXCEPT ![p] = clock[p] + 1]
       /\ lastHeard' = [lastHeard EXCEPT
                         ![p] = [ q \in Proc |-> lastHeard[p][q] + 1 ]]
       /\ UNCHANGED << timeout, outBox >>

\* ----------------------------------------------------------------------
\* Receive incoming alive messages
\* ----------------------------------------------------------------------
Receive(p, recSet) ==
    /\ \A m \in recSet: m \in Messages
    /\ \A m \in recSet: m.kind = "alive"
    /\ LET srcs == { m.src : m \in recSet } IN
       /\ clock' = [clock EXCEPT ![p] = clock[p] + 1]
       /\ lastHeard' = [lastHeard EXCEPT
                         ![p] = [ q \in Proc |-> IF q \in srcs THEN 0 ELSE lastHeard[p][q] ]]
       /\ suspicion' = [suspicion EXCEPT
                         ![p] = suspicion[p] \ srcs]
       /\ timeout' = [timeout EXCEPT
                       ![p] = [ q \in Proc |-> 
                                 IF q \in srcs /\ q \in suspicion[p]
                                 THEN timeout[p][q] + 1
                                 ELSE timeout[p][q] ]]
       /\ UNCHANGED outBox

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc: Send(p)
    \/ \E p \in Proc: Predict(p)
    \/ \E p \in Proc: 
         \E recSet \subseteq { m \in Messages : m.dst = p } :
            Receive(p, recSet)

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ suspicion \in [Proc -> SUBSET Proc]
    /\ timeout   \in [Proc -> [Proc -> Nat]]
    /\ lastHeard \in [Proc -> [Proc -> Nat]]
    /\ clock     \in [Proc -> Nat]
    /\ outBox    \in [Proc -> SUBSET Messages]
    /\ \A p \in Proc: suspicion[p] \subseteq Proc \ {p}

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_<< suspicion, timeout, lastHeard, clock, outBox >>

\* ----------------------------------------------------------------------
\* Invariants to be checked
\* ----------------------------------------------------------------------
INVARS == TypeOK

====