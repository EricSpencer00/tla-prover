---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
          NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M

vars == << Corr, Faulty, pc, rcvd, sent >>

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

FCConstraints ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

\* A correct process can receive any subset of the ECHO messages that were sent, and
\* any subset of the possible ECHO messages from the Byzantine processes.
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self) == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

\* A correct process may first receive ECHO messages from correct processes and later from Byzantine
\* processes; these are interleaved, since the network is asynchronous, and the number of messages
\* in rcvd[self] equals the number of distinct senders.
UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

\* This is the guarded action from the last if-then case of Figure 7 [1]. It is guarded by
\* Cardinality(rcvd'[self]) >= N - T, which does not hold when Cardinality(rcvd[self]) >= N - T,
\* so this action can never be enabled after the previous one.
UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self) \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self) \/ UponAcceptSentBefore(self)

CorrStep == \E self \in Corr : Step(self)

Spec == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

\* The safety property proved with TLAPS in the comment at the top of the file: if no correct
\* process ever broadcasts, then no correct process ever accepts.
Unforg == (\A i \in Proc : i \in Corr => (pc[i] # "AC"))

\* A small inductive invariant that is sufficient to imply Unforg. All the conjuncts apart from
\* pc = [ i \in Proc |-> "V0" ] are automatically established by Init and preserved by Next, so
\* the only "work" is showing the last conjunct is preserved.
IndInv_UnforgNoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

UMFS_CardinalityType ==
  \A X, Y, Z : /\ IsFiniteSet(X) /\ IsFiniteSet(Y) /\ IsFiniteSet(Z)
               /\ X \cup Y = Z /\ X = Z \ Y
               => Cardinality(X) = Cardinality(Z) - Cardinality(Y)

\* The full version of the invariant, for TLC: the last conjunct of IndInv_UnforgNoBcast
\* is placed first so that TLC evaluates it before the forms that can only hold in the
\* reachable subspace of InitNoBcast.
IndInv_UnforgNoBcastTLC ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] # "AC"
  /\ sent = {}
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

\* INIT => IndInv
InitNoBcast => IndInv_UnforgNoBcast
Init => FCConstraints /\ TypeOK

FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'

IndInv_UnforgNoBcast /\ [Next]_vars => IndInv_UnforgNoBcast'

IndInv_UnforgNoBcast' => (\A i \in Proc : i \in Corr => pc[i] # "AC")

SpecNoBcast => []Unforg

====