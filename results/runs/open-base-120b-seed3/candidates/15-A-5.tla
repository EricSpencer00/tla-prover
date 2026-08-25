---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* ----------------------------------------------------------------------
\* Process set
\* ----------------------------------------------------------------------
Proc == 1 .. N

\* ----------------------------------------------------------------------
\* Message definition (only ECHO messages)
\* ----------------------------------------------------------------------
Message == { << "ECHO", p >> : p \in Proc }

\* ----------------------------------------------------------------------
\* Variables
\* ----------------------------------------------------------------------
VARIABLES Correct, initRecvSet, pc, recv, sent

\* ----------------------------------------------------------------------
\* Derived definitions
\* ----------------------------------------------------------------------
Faulty == Proc \ Correct

ByzMsgs == { << "ECHO", f >> : f \in Faulty }

EchoSenders(p) == { m[2] : m \in recv[p] /\ m[1] = "ECHO" }

SentEcho(p) == << "ECHO", p >> \in sent

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ initRecvSet \subseteq Correct
    /\ sent = {}
    /\ recv = [p \in Proc |-> {}]
    /\ pc = [p \in Proc |-> 
            IF p \in Correct THEN 
                IF p \in initRecvSet THEN "Init" ELSE "NoInit"
            ELSE "NoInit"]

\* ----------------------------------------------------------------------
\* Actions
\* ----------------------------------------------------------------------
\* 1. Immediate accept and echo for processes that start with INIT
InitStep(p) ==
    /\ p \in Correct
    /\ pc[p] = "Init"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup { << "ECHO", p >> }
    /\ UNCHANGED <<Correct, initRecvSet, recv>>

\* 2. Receive an arbitrary (possibly empty) set of new messages
Receive(p, new) ==
    /\ p \in Correct
    /\ new \subseteq (sent \cup ByzMsgs) \ setdiff recv[p]
    /\ recv' = [recv EXCEPT ![p] = recv[p] \cup new]
    /\ UNCHANGED <<Correct, initRecvSet, pc, sent>>

\* 3. Send ECHO when enough distinct ECHO messages have been seen
SendEcho(p) ==
    /\ p \in Correct
    /\ ~SentEcho(p)
    /\ LET cnt == Cardinality(EchoSenders(p)) IN cnt >= N - 2 * T
    /\ pc' = [pc EXCEPT ![p] = "EchoSent"]
    /\ sent' = sent \cup { << "ECHO", p >> }
    /\ UNCHANGED <<Correct, initRecvSet, recv>>

\* 4. Accept when enough distinct ECHO messages have been seen
Accept(p) ==
    /\ p \in Correct
    /\ pc[p] # "Accepted"
    /\ LET cnt == Cardinality(EchoSenders(p)) IN cnt >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ UNCHANGED <<Correct, initRecvSet, recv, sent>>

Next ==
    \/ \E p \in Correct : InitStep(p)
    \/ \E p \in Correct, new \subseteq (sent \cup ByzMsgs) \ setdiff recv[p] : Receive(p, new)
    \/ \E p \in Correct : SendEcho(p)
    \/ \E p \in Correct : Accept(p)

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
vars == <<Correct, initRecvSet, pc, recv, sent>>

Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Invariants
\* ----------------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ initRecvSet \subseteq Correct
    /\ pc \in [Proc -> {"Init", "NoInit", "EchoSent", "Accepted"}]
    /\ recv \in [Proc -> SUBSET Message]
    /\ sent \in SUBSET Message

FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* ----------------------------------------------------------------------
\* LTL Properties
\* ----------------------------------------------------------------------
CorrLtl ==
    [] ( ( \A p \in Correct : pc[p] = "Init" )
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

RelayLtl ==
    [] ( ( \E p \in Correct : pc[p] = "Accepted")
        => <> ( \A p \in Correct : pc[p] = "Accepted") )

UnforgLtl ==
    [] ( ( \A p \in Correct : pc[p] = "NoInit")
        => [] ( \A p \in Correct : pc[p] # "Accepted") )

=============================================================================