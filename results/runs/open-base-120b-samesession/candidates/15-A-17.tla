---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process set and message definition
\* ----------------------------------------------------------------------
Proc == 1..N

Message == [type : {"ECHO"}, from : Proc]

AllMsgs == { [type |-> "ECHO", from |-> p] : p \in Proc }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES correct, faulty, initSet, echoSent, accepted, sent, recv

vars == << correct, faulty, initSet, echoSent, accepted, sent, recv >>

\* ----------------------------------------------------------------------
\* Type invariant
\* ----------------------------------------------------------------------
TypeOK ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ initSet \subseteq correct
    /\ echoSent \subseteq correct
    /\ accepted \subseteq correct
    /\ sent \subseteq AllMsgs
    /\ \A p \in correct : recv[p] \subseteq AllMsgs

\* ----------------------------------------------------------------------
\* Feasibility constraints
\* ----------------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ correct \subseteq Proc
    /\ Cardinality(correct) = N - F
    /\ faulty = Proc \ correct
    /\ initSet \subseteq correct
    /\ echoSent = {}
    /\ accepted = {}
    /\ sent = {}
    /\ recv = [p \in correct |-> {}]

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSend(p) == [type |-> "ECHO", from |-> p]

DistinctSenders(s) == { m.from : m \in s }

\* ----------------------------------------------------------------------
\* Action for a single correct process: receive any new messages and
\* possibly send an ECHO and/or accept according to the protocol.
\* ----------------------------------------------------------------------
ReceiveAct(p) ==
    /\ p \in correct
    /\ LET
          new   == SUBSET (AllMsgs \ recv[p])
          r'    == recv[p] \cup new
          sends == DistinctSenders(r')
          alreadyEcho == p \in echoSent
          alreadyAcc  == p \in accepted
          sendNow == IF p \in initSet
                       THEN TRUE
                    ELSE IF ~alreadyEcho
                       THEN IF Cardinality(sends) >= N - T
                               THEN TRUE
                            ELSE IF Cardinality(sends) >= N - 2 * T
                               THEN TRUE
                               ELSE FALSE
                       ELSE FALSE
          acceptNow == IF p \in initSet
                         THEN TRUE
                       ELSE IF ~alreadyEcho
                         THEN IF Cardinality(sends) >= N - T
                                 THEN TRUE
                              ELSE FALSE
                         ELSE IF alreadyEcho
                               THEN IF Cardinality(sends) >= N - T
                                      THEN TRUE
                                   ELSE FALSE
                               ELSE FALSE
       IN
       /\ recv' = [recv EXCEPT ![p] = r']
       /\ echoSent' = IF sendNow THEN echoSent \cup {p} ELSE echoSent
       /\ sent' = IF sendNow THEN sent \cup { EchoSend(p) } ELSE sent
       /\ accepted' = IF acceptNow THEN accepted \cup {p} ELSE accepted
       /\ UNCHANGED << correct, faulty, initSet >>

\* ----------------------------------------------------------------------
\* Next-state relation
\* ----------------------------------------------------------------------
Next ==
    \/ \E p \in correct : ReceiveAct(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* LTL properties
\* ----------------------------------------------------------------------
CorrLtl == [] ( (initSet = correct) => <> (accepted = correct) )

RelayLtl == [] ( ( \E p \in correct : p \in accepted ) => <> (accepted = correct) )

UnforgLtl == [] ( (initSet = {}) => [] (accepted = {}) )

\* ----------------------------------------------------------------------
\* THEOREMS (optional, for model checking)
\* ----------------------------------------------------------------------
THEOREM Spec => []TypeOK
THEOREM Spec => []FCConstraints

====