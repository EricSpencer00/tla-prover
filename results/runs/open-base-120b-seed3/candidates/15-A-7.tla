---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process set
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES
    Correct,          \* subset of Proc of correct processes
    Faulty,           \* complement of Correct
    initRecv,         \* correct processes that initially have the INIT message
    sentEcho,         \* correct processes that have sent an ECHO
    accepted,         \* correct processes that have accepted
    recvd             \* [p \in Proc |-> SUBSET Proc]  the set of senders whose ECHO p has received

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
AllSenders == Correct \cup Faulty

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ initRecv \subseteq Correct
    /\ sentEcho = {}
    /\ accepted = {}
    /\ recvd = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \E p \in Correct :
        \E newRecvd \in SUBSET AllSenders :
            /\ recvd[p] \subseteq newRecvd
            /\ newRecvd \subseteq (sentEcho \cup Faulty)      \* only messages that could have been sent
            /\ recvd' = [recvd EXCEPT ![p] = newRecvd]
            /\ sentEcho' =
                IF (p \in initRecv) \/
                   (p \notin sentEcho /\ Cardinality(newRecvd) >= N - 2 * T)
                THEN sentEcho \cup {p}
                ELSE sentEcho
            /\ accepted' =
                IF (p \in initRecv) \/
                   (p \notin sentEcho /\ Cardinality(newRecvd) >= N - T) \/
                   (p \in sentEcho /\ Cardinality(newRecvd) >= N - T)
                THEN accepted \cup {p}
                ELSE accepted
            /\ UNCHANGED <<Correct, Faulty, initRecv>>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_<<Correct, Faulty, initRecv, sentEcho, accepted, recvd>>
          /\ WF_<<Correct, Faulty, initRecv, sentEcho, accepted, recvd>>(Next)

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ initRecv \subseteq Correct
    /\ sentEcho \subseteq Correct
    /\ accepted \subseteq Correct
    /\ recvd \in [Proc -> SUBSET AllSenders]
    /\ \A p \in Proc : recvd[p] \subseteq AllSenders
    /\ \A p \in Correct : recvd[p] \subseteq (sentEcho \cup Faulty)

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == [] (initRecv = Correct => <> (accepted = Correct))

RelayLtl == [] ((\E p \in Correct : p \in accepted) => <> (accepted = Correct))

UnforgLtl == [] (initRecv = {} => [] (accepted = {}))

\* ----------------------------------------------------------------------
\* Theorems (optional, for TLC checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====