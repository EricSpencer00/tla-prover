---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

\* ----------------------------------------------------------------------
\* PARAMETERS
\* ----------------------------------------------------------------------
CONSTANTS N, T, F

\* The universe of process identifiers
PROCESSES == 1..N

\* ----------------------------------------------------------------------
\* STATE VARIABLES
\* ----------------------------------------------------------------------
VARIABLES
    Correct,          \* Set of correct processes
    Faulty,           \* Set of Byzantine processes
    initReceived,    \* Subset of Correct that initially got the INIT
    sent,            \* Subset of Correct that have sent an ECHO
    accepted,        \* Subset of Correct that have accepted
    rec               \* [p \in PROCESSES |-> SUBSET PROCESSES]   (ECHO senders received by p)

\* ----------------------------------------------------------------------
\* HELPER DEFINITIONS
\* ----------------------------------------------------------------------
vars == <<Correct, Faulty, initReceived, sent, accepted, rec>>

Cardinality(S) == Len(Seq(S))

\* ----------------------------------------------------------------------
\* INITIAL STATE
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq PROCESSES
    /\ Cardinality(Correct) = N - F
    /\ Faulty = PROCESSES \\ Correct
    /\ initReceived \subseteq Correct
    /\ sent = {}
    /\ accepted = {}
    /\ \A p \in PROCESSES : rec[p] = {}
    /\ TypeOK                     \* ensure domains are respected

\* ----------------------------------------------------------------------
\* ACTIONS
\* ----------------------------------------------------------------------
\* A correct process p receives any new set of ECHO messages (identified by senders)
Receive(p, new) ==
    /\ p \in Correct
    /\ new \subseteq PROCESSES \\ rec[p]
    /\ rec' = [rec EXCEPT ![p] = @ \cup new]
    /\ UNCHANGED <<Correct, Faulty, initReceived, sent, accepted>>

\* A correct process p sends an ECHO (if not already sent) and possibly accepts
EchoSend(p) ==
    /\ p \in Correct
    /\ p \notin sent
    /\ \* condition to be allowed to send an ECHO
       (p \in initReceived) \/ (Cardinality(rec[p]) >= N - 2*T)
    /\ sent' = sent \cup {p}
    /\ IF (p \in initReceived) \/ (Cardinality(rec[p]) >= N - T)
          THEN accepted' = accepted \cup {p}
          ELSE UNCHANGED accepted
    /\ UNCHANGED <<Correct, Faulty, initReceived, rec>>

\* A correct process p that has already sent an ECHO may accept once enough ECHOs are seen
Accept(p) ==
    /\ p \in Correct
    /\ p \in sent
    /\ p \notin accepted
    /\ Cardinality(rec[p]) >= N - T
    /\ accepted' = accepted \cup {p}
    /\ UNCHANGED <<Correct, Faulty, initReceived, sent, rec>>

\* Combined step for a particular correct process (used for fairness)
Step(p) ==
    \/ \E new \subseteq PROCESSES \\ rec[p] : Receive(p, new)
    \/ EchoSend(p)
    \/ Accept(p)

\* The overall next-state relation (any correct process may take a step)
Next ==
    \/ \E p \in Correct : Step(p)

\* ----------------------------------------------------------------------
\* SPECIFICATION
\* ----------------------------------------------------------------------
Spec ==
    Init /\ [][Next]_vars /\ \A p \in Correct : WF_vars(Receive(p, {}))

\* ----------------------------------------------------------------------
\* INVARIANTS
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq PROCESSES
    /\ Faulty = PROCESSES \\ Correct
    /\ initReceived \subseteq Correct
    /\ sent \subseteq Correct
    /\ accepted \subseteq Correct
    /\ \A p \in PROCESSES : rec[p] \subseteq PROCESSES
    /\ Cardinality(Correct) = N - F
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

FCConstraints ==
    /\ Cardinality(Faulty) = F
    /\ Cardinality(Correct) = N - F
    /\ N > 3 * T
    /\ T >= F

\* ----------------------------------------------------------------------
\* PROPERTIES (LTL)
\* ----------------------------------------------------------------------
\* If every correct process started with the INIT, eventually all accept
CorrLtl == [] (initReceived = Correct => <> (accepted = Correct))

\* If any correct process accepts, eventually all accept
RelayLtl == [] ( (\E p \in Correct : p \in accepted) => <> (accepted = Correct) )

\* If no correct process started with the INIT, no correct process ever accepts
UnforgLtl == [] ( initReceived = {} => [] (accepted = {}) )

\* ----------------------------------------------------------------------
\* THEOREMS (optional, can be used by the model checker)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====