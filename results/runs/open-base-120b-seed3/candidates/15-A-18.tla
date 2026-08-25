---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, TLC

CONSTANTS N, T, F

VARIABLES correct, faulty, pc, recv, sent

\* Process identifiers
Proc == 1..N

\* Message type (only ECHO)
Msg == [type : {"ECHO"}, from : Proc]

EchoFrom(p) == [type |-> "ECHO", from |-> p]

\* Number of distinct ECHO messages received by p
Count(p) == Cardinality({ q \in Proc : EchoFrom(q) \in recv[p] })

\* ----------------------------------------------------------------------
\* Initial state
Init ==
  /\ correct \subseteq Proc
  /\ Cardinality(correct) = N - F
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> {"NoInit", "InitReceived", "EchoSent", "Accepted"}]
  /\ \A p \in Proc :
        IF p \in correct
        THEN pc[p] \in {"NoInit", "InitReceived"}
        ELSE pc[p] = "NoInit"
  /\ recv \in [Proc -> SUBSET Msg]
  /\ \A p \in Proc : recv[p] = {}
  /\ sent = {}

\* ----------------------------------------------------------------------
\* Actions

\* A correct process nondeterministically receives new messages
Receive(p) ==
  /\ p \in correct
  /\ \E newSet \in SUBSET { EchoFrom(q) : q \in Proc } :
        recv' = [recv EXCEPT ![p] = recv[p] \cup newSet]
  /\ UNCHANGED <<pc, sent, correct, faulty>>

\* A correct process that initially got the INIT immediately accepts and sends ECHO
InitAccept(p) ==
  /\ p \in correct
  /\ pc[p] = "InitReceived"
  /\ pc' = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { EchoFrom(p) }
  /\ UNCHANGED <<recv, correct, faulty>>

\* A correct process that has not yet sent ECHO and sees enough (≥ N‑2T, < N‑T) ECHOs
SendEcho(p) ==
  /\ p \in correct
  /\ pc[p] = "NoInit"
  /\ Count(p) >= N - 2*T
  /\ Count(p) <  N - T
  /\ pc'   = [pc EXCEPT ![p] = "EchoSent"]
  /\ sent' = sent \cup { EchoFrom(p) }
  /\ UNCHANGED <<recv, correct, faulty>>

\* A correct process (whether it has already sent ECHO or not) sees ≥ N‑T ECHOs
SendEchoAndAccept(p) ==
  /\ p \in correct
  /\ (pc[p] = "NoInit" \/ pc[p] = "EchoSent")
  /\ Count(p) >= N - T
  /\ pc'   = [pc EXCEPT ![p] = "Accepted"]
  /\ sent' = sent \cup { EchoFrom(p) }
  /\ UNCHANGED <<recv, correct, faulty>>

Next ==
  \/ \E p \in correct : Receive(p)
  \/ \E p \in correct : InitAccept(p)
  \/ \E p \in correct : SendEcho(p)
  \/ \E p \in correct : SendEchoAndAccept(p)

\* ----------------------------------------------------------------------
\* Specification
Spec == Init /\ [][Next]_<<pc, recv, sent, correct, faulty>>

\* ----------------------------------------------------------------------
\* Type invariant
TypeOK ==
  /\ correct \subseteq Proc
  /\ faulty = Proc \ correct
  /\ pc \in [Proc -> {"NoInit", "InitReceived", "EchoSent", "Accepted"}]
  /\ recv \in [Proc -> SUBSET Msg]
  /\ sent \subseteq Msg

\* ----------------------------------------------------------------------
\* Constraints on constants
FCConstraints ==
  /\ N > 3 * T
  /\ T >= F
  /\ F >= 0
  /\ Cardinality(Proc) = N

\* ----------------------------------------------------------------------
\* Helper predicates for LTL properties
InitAll == \A p \in correct : pc[p] = "InitReceived"
InitNo  == \A p \in correct : pc[p] = "NoInit"

\* ----------------------------------------------------------------------
\* LTL properties
CorrLtl   == [] ( InitAll => <> ( \A p \in correct : pc[p] = "Accepted" ) )
RelayLtl  == [] ( ( \E p \in correct : pc[p] = "Accepted" ) => <> ( \A p \in correct : pc[p] = "Accepted" ) )
UnforgLtl == InitNo => [] ( \A p \in correct : pc[p] # "Accepted" )

=============================================================================