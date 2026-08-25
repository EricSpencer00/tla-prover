---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES Correct, Faulty, pc, recv, sent

\* ----------------------------------------------------------------------
\* Basic sets and messages
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ByzMsgs == {[type |-> "ECHO", from |-> q] : q \in Faulty}

SendEcho(p) == {[type |-> "ECHO", from |-> p]}

\* ----------------------------------------------------------------------
\* Type checking invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ sent \subseteq Message
    /\ recv \in [Proc -> SUBSET Message]
    /\ pc \in [Proc -> {"Init0","Init1","EchoSent","Accepted"}]

\* ----------------------------------------------------------------------
\* Fault‑containment constraints
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]
    /\ pc \in [Proc -> {"Init0","Init1","EchoSent","Accepted"}]
    /\ \A p \in Correct : pc[p] \in {"Init0","Init1"}
    /\ \A p \in Faulty : pc[p] = "Init0"
    /\ TypeOK

\* ----------------------------------------------------------------------
\* Action of a single correct process
\* ----------------------------------------------------------------------
Action(p) ==
    /\ p \in Correct
    /\ \E newMsgs \subseteq sent \cup ByzMsgs :
        LET recvNow   == recv[p] \cup newMsgs
            cnt       == Cardinality({ m.from : m \in recvNow /\ m.type = "ECHO"})
            pc0       == pc[p]
            newSent   ==
                IF (pc0 = "Init1") \/
                   (pc0 = "Init0" /\ cnt >= N - T) \/
                   (pc0 = "Init0" /\ cnt >= N - 2 * T /\ cnt < N - T) \/
                   (pc0 = "EchoSent" /\ cnt >= N - T)
                THEN sent \cup SendEcho(p)
                ELSE sent
            newPc ==
                IF pc0 = "Init1" THEN "Accepted"
                ELSE IF pc0 = "Init0" /\ cnt >= N - T THEN "Accepted"
                ELSE IF pc0 = "Init0" /\ cnt >= N - 2 * T /\ cnt < N - T THEN "EchoSent"
                ELSE IF pc0 = "EchoSent" /\ cnt >= N - T THEN "Accepted"
                ELSE pc0
        IN
        /\ recv' = [recv EXCEPT ![p] = recvNow]
        /\ sent' = newSent
        /\ pc'   = [pc EXCEPT ![p] = newPc]
        /\ UNCHANGED <<Correct, Faulty>>

\* ----------------------------------------------------------------------
\* Global next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Proc : Action(p)

\* ----------------------------------------------------------------------
\* Variables tuple for stuttering and fairness
\* ----------------------------------------------------------------------
vars == <<Correct, Faulty, pc, recv, sent>>

\* ----------------------------------------------------------------------
\* Specification (with weak fairness on each correct process's action)
\* ----------------------------------------------------------------------
Spec ==
    Init /\
    [][Next]_vars /\
    \A p \in Correct : WF_vars(Action(p))

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl ==
    [] ( ( \A p \in Correct : pc[p] = "Init1" ) => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

RelayLtl ==
    [] ( ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

UnforgLtl ==
    [] ( ( \A p \in Correct : pc[p] = "Init0" ) => ( \A p \in Correct : pc[p] # "Accepted" ) )

====