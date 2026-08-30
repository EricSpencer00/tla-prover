------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent, ByzMsgs
vars == << pc, rcvd, sent, Corr, Faulty, ByzMsgs >>

Assume == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }

Init == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr
  /\ ByzMsgs = Faulty \X M

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]

Step(self) ==
  /\ Receive(self, TRUE)
  /\ \/ (pc[self] = "V1" /\ pc' = [pc EXCEPT ![self] = "SE"] /\ sent' = sent \cup { <<self, "ECHO">> })
     \/ (pc[self] = "V0" /\ pc' = [pc EXCEPT ![self] = "SE"] /\ sent' = sent \cup { <<self, "ECHO">> })
     \/ (pc[self] = "V0" /\ pc' = [pc EXCEPT ![self] = "AC"] /\ sent' = sent \cup { <<self, "ECHO">> })
     \/ (pc[self] = "V1" /\ pc' = [pc EXCEPT ![self] = "AC"] /\ sent' = sent \cup { <<self, "ECHO">> })
     \/ UNCHANGED << pc, sent >>

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E self \in Corr: Receive(self, FALSE))

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]
  /\ ByzMsgs \subseteq Proc \X M

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC"))

Unforg_Step1 == InitNoBcast => IndInv_Unforg_NoBcast
Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
Unforg_Step4 == Spec => []Unforg

=============================================================================