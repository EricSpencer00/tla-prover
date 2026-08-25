---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* Constants
\* ----------------------------------------------------------------------
CONSTANT N, T, F

\* ----------------------------------------------------------------------
\* Derived sets
\* ----------------------------------------------------------------------
Proc == 1..N

Msg == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p, r) == { m.from : m \in r[p] /\ m.type = "ECHO" }

CanSendEcho(p, r) ==
    \/ pc[p] = "Init"
    \/ (pc[p] = "NoInit" /\ Cardinality(EchoSenders(p, r)) >= N - 2 * T)
    \/ (pc[p] = "NoInit" /\ Cardinality(EchoSenders(p, r)) >= N - T)
    \/ (pc[p] = "Echoed" /\ Cardinality(EchoSenders(p, r)) >= N - T)

NewPC(p, r) ==
    IF pc[p] = "Init" THEN "Accepted"
    ELSE IF pc[p] = "NoInit" THEN
          IF Cardinality(EchoSenders(p, r)) >= N - T THEN "Accepted"
          ELSE IF Cardinality(EchoSenders(p, r)) >= N - 2 * T THEN "Echoed"
          ELSE "NoInit"
          END
    ELSE IF pc[p] = "Echoed" THEN
          IF Cardinality(EchoSenders(p, r)) >= N - T THEN "Accepted"
          ELSE "Echoed"
          END
    ELSE pc[p] \* for Faulty processes

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ Cardinality(Correct) = N - F
    /\ Cardinality(Faulty) = F
    /\ pc \in [Proc -> {"NoInit", "Init", "Echoed", "Accepted", "Faulty"}]
    /\ \A p \in Correct : pc[p] \in {"NoInit", "Init"}
    /\ \A p \in Faulty : pc[p] = "Faulty"
    /\ recv \in [Proc -> SUBSET Msg]
    /\ \A p \in Proc : recv[p] = {}
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Correct :
        LET
            ByzMsgs == { [type |-> "ECHO", from |-> f] : f \in Faulty }
            NewMsgs == SUBSET( sent \cup ByzMsgs )
            recv2  == [recv EXCEPT ![p] = recv[p] \cup NewMsgs]
            pcNew  == NewPC(p, recv2)
            send   == CanSendEcho(p, recv2)
            sent2  == IF send THEN sent \cup { [type |-> "ECHO", from |-> p] } ELSE sent
        IN
            /\ recv' = recv2
            /\ pc'   = [pc EXCEPT ![p] = pcNew]
            /\ sent' = sent2
            /\ UNCHANGED <<Correct, Faulty>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Type invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Faulty = Proc \ Correct
    /\ Cardinality(Correct) = N - F
    /\ Cardinality(Faulty) = F
    /\ pc \in [Proc -> {"NoInit","Init","Echoed","Accepted","Faulty"}]
    /\ sent \subseteq Msg
    /\ recv \in [Proc -> SUBSET Msg]

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
    [] ( ( \A p \in Correct : pc[p] = "Init" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

RelayLtl ==
    [] ( ( \E p \in Correct : pc[p] = "Accepted" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

UnforgLtl ==
    ( Init /\ ( \A p \in Correct : pc[p] = "NoInit" ) )
        => [] ( \A p \in Correct : pc[p] # "Accepted" )

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => FCConstraints

====