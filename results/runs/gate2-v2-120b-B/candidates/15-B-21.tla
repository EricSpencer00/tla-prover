---- MODULE bcastByz ----
EXTENDS Naturals,
        FiniteSets,
        Functions,
        FunctionTheorems,
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

\* ----------------------------------------------------------------------
\*  Assumptions about the parameters
\* ----------------------------------------------------------------------
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0

\* ----------------------------------------------------------------------
\*  Derived constants
\* ----------------------------------------------------------------------
Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M          \* Byzantine messages (pairs of faulty process and "ECHO")

\* ----------------------------------------------------------------------
\*  State variables
\* ----------------------------------------------------------------------
vars == << pc, rcvd, sent, Corr, Faulty >>

\* ----------------------------------------------------------------------
\*  Initial state
\* ----------------------------------------------------------------------
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

\* ----------------------------------------------------------------------
\*  Restricted initial state used for the unforgeability property
\* ----------------------------------------------------------------------
InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

\* ----------------------------------------------------------------------
\*  Helper action: a process may receive any subset of the messages that are
\*  currently in the system (including Byzantine messages if includeByz = TRUE)
\* ----------------------------------------------------------------------
Receive(self, includeByz) ==
  \E new \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup new ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

\* ----------------------------------------------------------------------
\*  Process steps (exactly the actions from Figure 7 of the paper)
\* ----------------------------------------------------------------------
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - 2 * T
  /\ Cardinality(rcvd[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ UNCHANGED << Corr, Faulty, sent, rcvd >>

\* ----------------------------------------------------------------------
\*  A single step of a correct process
\* ----------------------------------------------------------------------
Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

\* ----------------------------------------------------------------------
\*  Global transition relation
\* ----------------------------------------------------------------------
Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

\* ----------------------------------------------------------------------
\*  Specification (safety only, no fairness needed)
\* ----------------------------------------------------------------------
SpecNoBcast == InitNoBcast /\ [][Next]_vars

\* ----------------------------------------------------------------------
\*  Type correctness (kept for model checking)
\* ----------------------------------------------------------------------
TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

\* ----------------------------------------------------------------------
\*  Unforgeability property (safety)
\* ----------------------------------------------------------------------
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

\* ----------------------------------------------------------------------
\*  Inductive invariant used in the proof
\* ----------------------------------------------------------------------
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

=============================================================================