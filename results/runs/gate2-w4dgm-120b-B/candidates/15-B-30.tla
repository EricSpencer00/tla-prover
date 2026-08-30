------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

Init == /\ sent = {}
        /\ pc \in [ Proc -> {"V0", "V1"} ]
        /\ rcvd = [ i \in Proc |-> {} ]
        /\ Corr \in SUBSET Proc
        /\ Cardinality(Corr) = N - F
        /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

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

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) == \/ ReceiveFromAnySender(self)
             /\ \/ UponV1(self)
                \/ UponNonFaulty(self)
                \/ UponAcceptNotSentBefore(self)
                \/ UponAcceptSentBefore(self)

Next == \/ \E self \in Corr: Step(self)
        \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

TypeOK == /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
          /\ Corr \subseteq Proc
          /\ Faulty \subseteq Proc
          /\ sent \subseteq Proc \X M
          /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

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

Unforg == (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints

THEOREM Unforg_Step1 == InitNoBcast => (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints
PROOF <1>1 InitNoBcast => (\A i \in Proc: i \in Corr => (pc[i] # "AC"))
    BY (ASSUME InitNoBcast PROVE (\A i \in Proc: i \in Corr => (pc[i] # "AC")) OBVIOUS)
<1>2 InitNoBcast => FCConstraints
    BY FCConstraints_TypeOK_InitNoBcast
<1> QED

THEOREM Unforg_Step2 == (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints /\ [Next]_vars => (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints'
PROOF
  <1>1 (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints /\ [Next]_vars => (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints' /\ sent = {}
      BY <2>1, <2>2 DEF FCConstraints
  <1>2 (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints /\ [Next]_vars => (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints'
      <2>1 (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints /\ [Next]_vars => (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints'
        BY <1>1
  <1>3 (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints /\ [Next]_vars => (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints'
        BY <2>1
  <1> QED

THEOREM Unforg_Step3 == (\A i \in Proc: i \in Corr => (pc[i] # "AC")) /\ FCConstraints => Unforg
  BY <1>1 DEF Unforg

=============================================================================