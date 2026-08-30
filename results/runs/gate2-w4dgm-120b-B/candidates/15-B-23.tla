------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems, 
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
Vars == << pc, rcvd, sent, Corr, Faulty >>
vars == << pc, rcvd, sent, Corr, Faulty >>

TypeOK == / Corr \subseteq Proc
           /\ Faulty \subseteq Proc
           /\ IsFiniteSet(Corr)
           /\ IsFiniteSet(Faulty)
           /\ sent \subseteq Proc \X M
           /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
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

Step(self) == Receive(self, TRUE) /\ \/ UponV1(self) \/ UponNonFaulty(self) 
              \/ UponAcceptNotSentBefore(self) \/ UponAcceptSentBefore(self)

Next == \E self \in Corr: Step(self) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(\E self \in Corr: Receive(self, FALSE)
                                            /\ \/ UponV1(self) \/ UponNonFaulty(self)
                                            \/ UponAcceptNotSentBefore(self) \/ UponAcceptSentBefore(self))

Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC"))

IndInv_Unforg_NoBcast == TypeOK /\ sent = {} /\ pc = [ i \in Proc |-> "V0" ]

UNFORG_PROOF == Spec => []Unforg
=============================================================================