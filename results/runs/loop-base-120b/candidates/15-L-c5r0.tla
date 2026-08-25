---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

\* -----------------------------------------------------------------
\* Process set
\* -----------------------------------------------------------------
Proc == 1 .. N

\* -----------------------------------------------------------------
\* Variables
\* -----------------------------------------------------------------
VARIABLES Correct, Faulty, pc, recv, sent

vars == <<Correct, Faulty, pc, recv, sent>>

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
PCVals == {"NoInit", "InitRecv", "SentEcho", "Accepted"}

CountEcho(p) == Cardinality(recv[p])

PossibleMsgs(p) == (sent \cup Faulty) \ recv[p]   \* messages that p has not yet received

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> PCVals]
    /\ \A p \in Proc : pc[p] \in {"NoInit", "InitRecv"}
    /\ recv \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : recv[p] = {}
    /\ sent = {}

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
Receive(p) ==
    /\ p \in Correct
    /\ LET newMsgs == PossibleMsgs(p) IN
       recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ UNCHANGED <<Correct, Faulty, pc, sent>>

EchoAndAccept(p) ==
    /\ p \in Correct
    /\ pc[p] = "InitRecv"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<Correct, Faulty, recv>>

SendEcho(p) ==
    /\ p \in Correct
    /\ pc[p] \in {"NoInit", "InitRecv"}   \* has not sent ECHO yet
    /\ CountEcho(p) >= N - 2 * T
    /\ pc' = [pc EXCEPT ![p] = "SentEcho"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<Correct, Faulty, recv>>

Accept(p) ==
    /\ p \in Correct
    /\ pc[p] # "Accepted"
    /\ CountEcho(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = IF p \in sent THEN sent ELSE sent \cup {p}
    /\ UNCHANGED <<Correct, Faulty, recv>>

Next ==
    \/ \E p \in Correct : Receive(p)
    \/ \E p \in Correct : EchoAndAccept(p)
    \/ \E p \in Correct : SendEcho(p)
    \/ \E p \in Correct : Accept(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -----------------------------------------------------------------
\* Type invariant
\* -----------------------------------------------------------------
TypeOK ==
    /\ Correct \subseteq Proc
    /\ Cardinality(Correct) = N - F
    /\ Faulty = Proc \ Correct
    /\ pc \in [Proc -> PCVals]
    /\ recv \in [Proc -> SUBSET Proc]
    /\ sent \subseteq Correct

\* -----------------------------------------------------------------
\* Fault‑containment constraints
\* -----------------------------------------------------------------
FCConstraints ==
    /\ N > 3 * T
    /\ T >= F
    /\ F >= 0

\* -----------------------------------------------------------------
\* Liveness properties (expressed as state predicates for TLC)
\* -----------------------------------------------------------------
CorrLtl ==
    ( \A p \in Correct : pc[p] = "InitRecv" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

RelayLtl ==
    ( \E p \in Correct : pc[p] = "Accepted" ) => <> ( \A p \in Correct : pc[p] = "Accepted" )

UnforgLtl ==
    ( \A p \in Correct : pc[p] = "NoInit" ) => [] ( \A p \in Correct : pc[p] # "Accepted" )

=============================================================================