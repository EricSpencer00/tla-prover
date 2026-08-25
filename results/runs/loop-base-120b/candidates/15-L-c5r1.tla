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
VARIABLES CorrectSet, FaultySet, pc, recv, sent

vars == <<CorrectSet, FaultySet, pc, recv, sent>>

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
PCVals == {"NoInit", "InitRecv", "SentEcho", "Accepted"}

CountEcho(p) == Cardinality(recv[p])

PossibleMsgs(p) == (sent \cup FaultySet) \ recv[p]   \* messages that p has not yet received

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ CorrectSet \subseteq Proc
    /\ Cardinality(CorrectSet) = N - F
    /\ FaultySet = Proc \ CorrectSet
    /\ pc \in [Proc -> PCVals]
    /\ \A p \in Proc : pc[p] \in {"NoInit", "InitRecv"}
    /\ recv \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : recv[p] = {}
    /\ sent = {}

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
Receive(p) ==
    /\ p \in CorrectSet
    /\ LET newMsgs == PossibleMsgs(p) IN
       recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ UNCHANGED <<CorrectSet, FaultySet, pc, sent>>

EchoAndAccept(p) ==
    /\ p \in CorrectSet
    /\ pc[p] = "InitRecv"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<CorrectSet, FaultySet, recv>>

SendEcho(p) ==
    /\ p \in CorrectSet
    /\ pc[p] \in {"NoInit", "InitRecv"}   \* has not sent ECHO yet
    /\ CountEcho(p) >= N - 2 * T
    /\ pc' = [pc EXCEPT ![p] = "SentEcho"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<CorrectSet, FaultySet, recv>>

Accept(p) ==
    /\ p \in CorrectSet
    /\ pc[p] # "Accepted"
    /\ CountEcho(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = IF p \in sent THEN sent ELSE sent \cup {p}
    /\ UNCHANGED <<CorrectSet, FaultySet, recv>>

Next ==
    \/ \E p \in CorrectSet : Receive(p)
    \/ \E p \in CorrectSet : EchoAndAccept(p)
    \/ \E p \in CorrectSet : SendEcho(p)
    \/ \E p \in CorrectSet : Accept(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -----------------------------------------------------------------
\* Type invariant
\* -----------------------------------------------------------------
TypeOK ==
    /\ CorrectSet \subseteq Proc
    /\ Cardinality(CorrectSet) = N - F
    /\ FaultySet = Proc \ CorrectSet
    /\ pc \in [Proc -> PCVals]
    /\ recv \in [Proc -> SUBSET Proc]
    /\ sent \subseteq CorrectSet

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
    ( \A p \in CorrectSet : pc[p] = "InitRecv" ) => <> ( \A p \in CorrectSet : pc[p] = "Accepted" )

RelayLtl ==
    ( \E p \in CorrectSet : pc[p] = "Accepted" ) => <> ( \A p \in CorrectSet : pc[p] = "Accepted" )

UnforgLtl ==
    ( \A p \in CorrectSet : pc[p] = "NoInit" ) => [] ( \A p \in CorrectSet : pc[p] # "Accepted" )

=============================================================================