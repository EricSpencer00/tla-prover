---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

\* ----------------------------------------------------------------------
\* Assumptions on the parameters
\* ----------------------------------------------------------------------
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
               (N > 3 * T) /\ (T >= F) /\ (F >= 0) /\ (N - 2 * T >= T + 1)

\* ----------------------------------------------------------------------
\* Derived constants
\* ----------------------------------------------------------------------
Proc == 1 .. N               \* All process identifiers
M == {"ECHO"}                \* The only message type
ByzMsgs == Faulty \X M       \* Messages that a Byzantine process may send

vars == << Corr, Faulty, pc, rcvd, sent >>

\* ----------------------------------------------------------------------
\* Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ sent = {}
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ rcvd = [i \in Proc |-> {}]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

\* The special initial condition for the unforgeability property
InitNoBcast == pc \in [Proc -> {"V0"}] /\ Init

\* ----------------------------------------------------------------------
\* Helper definitions
\* ----------------------------------------------------------------------
Receive(self, includeByz) ==
  \E newMsgs \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [i \in Proc |-> IF i = self THEN rcvd[i] \cup newMsgs ELSE rcvd[i]]

ReceiveFromAnySender(self) == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty, rcvd>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
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
  /\ sent' = sent
  /\ UNCHANGED <<Corr, Faulty>>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

\* ----------------------------------------------------------------------
\* Specification
\* ----------------------------------------------------------------------
Spec == Init /\ [][Next]_vars

\* ----------------------------------------------------------------------
\* Safety property (unforgeability)
\* ----------------------------------------------------------------------
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

\* ----------------------------------------------------------------------
\* Inductive invariant used for the proof
\* ----------------------------------------------------------------------
IndInv_Unforg_NoBcast ==
  /\ pc = [i \in Proc |-> "V0"]
  /\ sent = {}
  /\ TypeOK

\* ----------------------------------------------------------------------
\* Type correctness predicate
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]
  /\ Corr \subseteq Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) = N - F

\* ----------------------------------------------------------------------
\* Theorems (kept for completeness; proofs are omitted here)
\* ----------------------------------------------------------------------
THEOREM Spec => []Unforg

=============================================================================