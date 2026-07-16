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

VARIABLES Corr,            \* the set of correct processes
          Faulty,          \* the set of faulty processes
          pc,              \* control state of each process
          rcvd,            \* messages received by each process
          sent             \* messages sent by correct processes

\* Ensure the parameters satisfy the required constraints
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0) /\ N - 2*T >= T + 1

Proc == 1 .. N               \* all processes, including the faulty ones
M    == {"ECHO"}             \* the only message type
ByzMsgs == Faulty \X M       \* Byzantine messages (one per faulty process)

vars == << Corr, Faulty, pc, rcvd, sent >>

\* Initial state: no messages sent, each process is either V0 or V1,
\* and the partition into correct and faulty processes is chosen nondeterministically
Init ==
  /\ sent = {}                          
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]       
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F           
  /\ Faulty = Proc \ Corr               

\* Special restricted initial state used for the unforgeability property
InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ] 
  /\ Init

\* Receive a (possibly empty) set of new messages; the set may include Byzantine messages
Receive(self, includeByz) ==
  \E newMess \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {} ) ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMess ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)     == Receive(self, TRUE)

\* Process steps
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty, rcvd >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ (UponV1(self)
      \/ UponNonFaulty(self)
      \/ UponAcceptNotSentBefore(self)
      \/ UponAcceptSentBefore(self))

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

\* Fairness needed only for liveness properties
Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(\E self \in Corr : /\ ReceiveFromCorrectSender(self)
                               /\ (UponV1(self)
                                   \/ UponNonFaulty(self)
                                   \/ UponAcceptNotSentBefore(self)
                                   \/ UponAcceptSentBefore(self)))

\* Safety‑only version (used for checking Unforgeability)
SpecNoBcast == InitNoBcast /\ [][Next]_vars

\* Type correctness
TypeOK ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

\* Cardinality constraints used throughout the proofs
FCConstraints ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ IsFiniteSet(Corr)
  /\ IsFiniteSet(Faulty)
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

\* Safety property: no correct process ever accepts
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

\* Inductive invariant used for the proof
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

=============================================================================