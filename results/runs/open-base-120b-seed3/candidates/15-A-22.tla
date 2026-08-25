---- MODULE bcastByz ----
EXTENDS Naturals, Sequences, TLC, Temporal

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Types and basic sets
\* ----------------------------------------------------------------------
Proc == 1..N

Msg == [sender : Proc, type : {"ECHO"}]

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, Faulty, pc, received, sent

vars == <<Correct, Faulty, pc, received, sent>>

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
EchoSenders(p) == { m.sender : m \in received[p] }

PossibleByzantineMsgs == { [sender |-> f, type |-> "ECHO"] : f \in Faulty }

PossibleRecv(p) ==
    (sent \cup PossibleByzantineMsgs) \ received[p]

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Correct -> {"InitYes", "InitNo"}]
    /\ received = [p \in Correct |-> {}]
    /\ sent = {}

\* ----------------------------------------------------------------------
\* Receive action (nondeterministically receive any subset of possible msgs)
\* ----------------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ LET poss == PossibleRecv(p) IN
       \E new \in SUBSET poss :
           /\ received' = [received EXCEPT ![p] = received[p] \cup new]
           /\ UNCHANGED <<Correct, Faulty, pc, sent>>

\* ----------------------------------------------------------------------
\* Actions that cause a correct process to send an ECHO (and possibly accept)
\* ----------------------------------------------------------------------
SendEchoInit(p) ==
    /\ p \in Correct
    /\ pc[p] = "InitYes"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
    /\ UNCHANGED <<Correct, Faulty, received>>

SendEchoAccept(p) ==
    /\ p \in Correct
    /\ pc[p] = "InitNo"
    /\ Cardinality(EchoSenders(p)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
    /\ UNCHANGED <<Correct, Faulty, received>>

SendEchoNoAccept(p) ==
    /\ p \in Correct
    /\ pc[p] = "InitNo"
    /\ Cardinality(EchoSenders(p)) >= N - 2 * T
    /\ Cardinality(EchoSenders(p)) < N - T
    /\ pc' = [pc EXCEPT ![p] = "Echoed"]
    /\ sent' = sent \cup { [sender |-> p, type |-> "ECHO"] }
    /\ UNCHANGED <<Correct, Faulty, received>>

AcceptAfterEcho(p) ==
    /\ p \in Correct
    /\ pc[p] = "Echoed"
    /\ Cardinality(EchoSenders(p)) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<sent, received, Correct, Faulty>>

\* ----------------------------------------------------------------------
\* The combined step for a correct process (receive then possibly act)
\* ----------------------------------------------------------------------
ProcStep(p) == \/ Receive(p) \/ SendEchoInit(p) \/ SendEchoAccept(p) \/ SendEchoNoAccept(p) \/ AcceptAfterEcho(p)

Next == \E p \in Correct : ProcStep(p)

\* ----------------------------------------------------------------------
\* Weak fairness for the combined step of any correct process
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(\E p \in Correct : ProcStep(p))

\* ----------------------------------------------------------------------
\* Invariant: type correctness
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Correct -> {"InitYes", "InitNo", "Echoed", "Accepted"}]
    /\ received \in [Correct -> SUBSET Msg]
    /\ sent \subseteq Msg
    /\ \A m \in sent : m.type = "ECHO" /\ m.sender \in Correct

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
CorrLtl ==
    [] ( ( \A p \in Correct : pc[p] = "InitYes" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

RelayLtl ==
    [] ( ( \E p \in Correct : pc[p] = "Accepted" )
        => <> ( \A p \in Correct : pc[p] = "Accepted" ) )

UnforgLtl ==
    [] ( ( \A p \in Correct : pc[p] = "InitNo" )
        => [] ( \A p \in Correct : pc[p] # "Accepted" ) )

====