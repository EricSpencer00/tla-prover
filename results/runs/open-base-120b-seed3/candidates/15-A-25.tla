---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process identifiers
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages)
\* ----------------------------------------------------------------------
ECHO == "ECHO"

Message == [type : {"ECHO"}, from : Proc]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, sent, recv

vars == << Correct, Faulty, pc, sent, recv >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"init_yes", "init_no", "echo_sent", "accepted"}]
    /\ \A p \in Correct : pc[p] \in {"init_yes", "init_no"}
    /\ \A p \in Faulty : pc[p] = "init_no"      \* value irrelevant for faulty
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
ByzMsgs == { [type |-> ECHO, from |-> f] : f \in Faulty }

AllPossibleMsgs == sent \cup ByzMsgs

EchoSenders(set) == { m.from : m \in set /\ m.type = ECHO }

\* ----------------------------------------------------------------------
\* Receive-and‑act step of a correct process p
\* ----------------------------------------------------------------------
ReceiveAct(p) ==
    /\ p \in Correct
    /\ \E newSet \in SUBSET (AllPossibleMsgs \ recv[p]) :
        LET newRecv == recv[p] \cup newSet IN
        LET eSenders == EchoSenders(newRecv) IN
        LET pcPrime ==
            CASE pc[p] = "init_yes"                         -> [pc EXCEPT ![p] = "accepted"]
                 pc[p] = "init_no" /\ Cardinality(eSenders) >= N - T
                                                             -> [pc EXCEPT ![p] = "accepted"]
                 pc[p] = "init_no" /\ Cardinality(eSenders) >= N - 2 * T
                                                             -> [pc EXCEPT ![p] = "echo_sent"]
                 pc[p] = "echo_sent" /\ Cardinality(eSenders) >= N - T
                                                             -> [pc EXCEPT ![p] = "accepted"]
                 OTHER                                      -> pc
        IN
        LET sentPrime ==
            CASE pc[p] \in {"init_yes", "init_no"} /\ 
                 ( (pc[p] = "init_no" /\ Cardinality(eSenders) >= N - T) \/
                   (pc[p] = "init_no" /\ Cardinality(eSenders) >= N - 2 * T) \/
                   pc[p] = "init_yes")
                                                             -> sent \cup { [type |-> ECHO, from |-> p] }
                 OTHER                                      -> sent
        IN
        /\ pc' = pcPrime
        /\ sent' = sentPrime
        /\ recv' = [recv EXCEPT ![p] = newRecv]
        /\ UNCHANGED <<Correct, Faulty>>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in Correct : ReceiveAct(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* ----------------------------------------------------------------------
\* Invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> {"init_yes", "init_no", "echo_sent", "accepted"}]
    /\ sent \subseteq { [type |-> ECHO, from |-> p] : p \in Correct }
    /\ recv \in [Proc -> SUBSET { [type |-> ECHO, from |-> p] : p \in Proc }]

\* ----------------------------------------------------------------------
\* Invariant: fault‑tolerance constraints
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == [] ( (\A p \in Correct : pc[p] = "init_yes") => <> ( \A p \in Correct : pc[p] = "accepted") )

RelayLtl == [] ( (\E p \in Correct : pc[p] = "accepted") => <> ( \A p \in Correct : pc[p] = "accepted") )

UnforgLtl == [] ( (\A p \in Correct : pc[p] = "init_no") => [] ( \A p \in Correct : pc[p] # "accepted") )

====