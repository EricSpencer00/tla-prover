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
VARIABLES Corrects, Faultys, pc, recv, sent

vars == <<Corrects, Faultys, pc, recv, sent>>

\* -----------------------------------------------------------------
\* Helper definitions
\* -----------------------------------------------------------------
PCVals == {"NoInit", "InitRecv", "SentEcho", "Accepted"}

CountEcho(p) == Cardinality(recv[p])

PossibleMsgs(p) == (sent \cup Faultys) \ recv[p]   \* messages that p has not yet received

\* -----------------------------------------------------------------
\* Initialization
\* -----------------------------------------------------------------
Init ==
    /\ Corrects = { i \in Proc : i <= N - F }            \* deterministic correct set
    /\ Faultys = Proc \ Corrects
    /\ pc \in [Proc -> PCVals]
    /\ \A p \in Proc : pc[p] \in {"NoInit", "InitRecv"}
    /\ recv \in [Proc -> SUBSET Proc]
    /\ \A p \in Proc : recv[p] = {}
    /\ sent = {}

\* -----------------------------------------------------------------
\* Actions
\* -----------------------------------------------------------------
Receive(p) ==
    /\ p \in Corrects
    /\ LET newMsgs == PossibleMsgs(p) IN
         recv' = [recv EXCEPT ![p] = recv[p] \cup newMsgs]
    /\ UNCHANGED <<Corrects, Faultys, pc, sent>>

EchoAndAccept(p) ==
    /\ p \in Corrects
    /\ pc[p] = "InitRecv"
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<Corrects, Faultys, recv>>

SendEcho(p) ==
    /\ p \in Corrects
    /\ pc[p] \in {"NoInit", "InitRecv"}   \* has not sent ECHO yet
    /\ CountEcho(p) >= N - 2 * T
    /\ pc' = [pc EXCEPT ![p] = "SentEcho"]
    /\ sent' = sent \cup {p}
    /\ UNCHANGED <<Corrects, Faultys, recv>>

Accept(p) ==
    /\ p \in Corrects
    /\ pc[p] # "Accepted"
    /\ CountEcho(p) >= N - T
    /\ pc' = [pc EXCEPT ![p] = "Accepted"]
    /\ sent' = IF p \in sent THEN sent ELSE sent \cup {p}
    /\ UNCHANGED <<Corrects, Faultys, recv>>

Next ==
    \/ \E p \in Corrects : Receive(p)
    \/ \E p \in Corrects : EchoAndAccept(p)
    \/ \E p \in Corrects : SendEcho(p)
    \/ \E p \in Corrects : Accept(p)

\* -----------------------------------------------------------------
\* Specification
\* -----------------------------------------------------------------
Spec == Init /\ [][Next]_vars /\ WF_vars(Next)

\* -----------------------------------------------------------------
\* Type invariant
\* -----------------------------------------------------------------
TypeOK ==
    /\ Corrects \subseteq Proc
    /\ Cardinality(Corrects) = N - F
    /\ Faultys = Proc \ Corrects
    /\ pc \in [Proc -> PCVals]
    /\ recv \in [Proc -> SUBSET Proc]
    /\ sent \subseteq Corrects

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
    ( \A p \in Corrects : pc[p] = "InitRecv" ) => <> ( \A p \in Corrects : pc[p] = "Accepted" )

RelayLtl ==
    ( \E p \in Corrects : pc[p] = "Accepted" ) => <> ( \A p \in Corrects : pc[p] = "Accepted" )

UnforgLtl ==
    ( \A p \in Corrects : pc[p] = "NoInit" ) => [] ( \A p \in Corrects : pc[p] # "Accepted" )

=============================================================================