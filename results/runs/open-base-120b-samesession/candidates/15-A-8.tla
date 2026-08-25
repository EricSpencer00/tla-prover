---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANT N, T, F

\* ----------------------------------------------------------------------
\* Process set
\* ----------------------------------------------------------------------
Proc == 1..N

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, Sent

vars == <<Correct, Faulty, pc, recv, Sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
PCVals == {"Init0", "Init1", "Echoed", "Accepted"}

\* Number of distinct ECHO senders a process p has received
EchoCount(p) == Cardinality(recv[p])

\* ----------------------------------------------------------------------
\* Initialization
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ Sent = {}
    /\ pc \in [Proc -> {"Init0","Init1"}]          \* each correct process may start with or without INIT
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* One step of a correct process p
\* ----------------------------------------------------------------------
ProcStep(p) ==
    /\ p \in Correct
    /\ LET Avail == (Sent \cup Faulty) \ recv[p] IN
       \E newMsgs \in SUBSET(Avail) :
            /\ recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
            /\ LET recSet == recv'[p] IN
               /\ Sent' = IF (pc[p] = "Init1")                 \* case (2)
                         \/ (pc[p] = "Init0" /\ Cardinality(recSet) >= N - T)   \* case (4)
                         \/ (pc[p] = "Init0" /\ Cardinality(recSet) >= N - 2*T
                                 /\ Cardinality(recSet) <  N - T)               \* case (3)
                         \/ (pc[p] = "Echoed" /\ Cardinality(recSet) >= N - T) \* case (5)
                         THEN Sent \cup {p}
                         ELSE Sent
               /\ pc' = IF pc[p] = "Init1" THEN "Accepted"
                         ELSE IF pc[p] = "Init0" /\ Cardinality(recSet) >= N - T
                                 THEN "Accepted"
                         ELSE IF pc[p] = "Init0" /\ Cardinality(recSet) >= N - 2*T
                                 /\ Cardinality(recSet) < N - T
                                 THEN "Echoed"
                         ELSE IF pc[p] = "Echoed" /\ Cardinality(recSet) >= N - T
                                 THEN "Accepted"
                         ELSE pc[p]
    /\ UNCHANGED <<Correct, Faulty>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Correct : ProcStep(p)
    \/ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ \A p \in Correct : WF_vars(ProcStep(p))

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ Sent \subseteq Correct
    /\ pc \in [Proc -> PCVals]
    /\ recv \in [Proc -> SUBSET Proc]

\* ----------------------------------------------------------------------
\* Fault‑containment constraints
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Liveness properties (expressed as temporal formulas)
\* ----------------------------------------------------------------------
CorrLtl ==
    ( \A p \in Correct : pc[p] = "Init1" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl ==
    ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl ==
    ( \A p \in Correct : pc[p] = "Init0" ) => [] ( \A p \in Correct : pc[p] /= "Accepted" )

=============================================================================