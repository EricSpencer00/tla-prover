---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

\* ----------------------------------------------------------------------
\* Auxiliary definitions
\* ----------------------------------------------------------------------
Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Init ==
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == Init

Receive(self, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i] ]

ReceiveFromAnySender(self) == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty, rcvd>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED <<sent, Corr, Faulty, rcvd>>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Type correctness (kept for completeness)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc

\* ----------------------------------------------------------------------
\* Safety property: Unforgeability
\* ----------------------------------------------------------------------
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

\* ----------------------------------------------------------------------
\* Inductive invariant (reordered for TLC efficiency)
\* ----------------------------------------------------------------------
IndInv_Unforg_NoBcast_TLC ==
  /\ pc = [i \in Proc |-> "V0"]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ sent = {}
  /\ rcvd \in [Proc -> SUBSET ByzMsgs]

=============================================================================