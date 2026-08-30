------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == { <<p, "ECHO">> : p \in Faulty }

VARIABLES Corr, Faulty, pc, rcvd, sent
vars == << pc, rcvd, sent, Corr, Faulty >>

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

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self) == Receive(self, TRUE)

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

Step(self) == 
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars /\ WF_vars(\E self \in Corr:
                                           /\ ReceiveFromCorrectSender(self)
                                           /\ \/ UponV1(self)
                                              \/ UponNonFaulty(self)
                                              \/ UponAcceptNotSentBefore(self)
                                              \/ UponAcceptSentBefore(self))

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M
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

Unforg == (\A i \in Proc: i \in Corr => (pc[i] # "AC"))

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

TheoremInitNoBcast ==
  InitNoBcast => IndInv_Unforg_NoBcast
  <1> SUFFICES ASSUME InitNoBcast PROVE IndInv_Unforg_NoBcast
       OBVIOUS

NextStep ==
  /\ IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <3>1 IndInv_Unforg_NoBcast' = /\ TypeOK' /\ FCConstraints' /\ sent' = {} /\ pc' = [i \in Proc |-> "V0"]
       BY DEF IndInv_Unforg_NoBcast
  <3>2 CASE UNCHANGED vars
       <4>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
            BY DEF IndInv_Unforg_NoBcast, vars
       <4>2 (\E i \in Corr : Step(i)) => IndInv_Unforg_NoBcast'
            <5>1 ASSUME IndInv_Unforg_NoBcast, \E i \in Corr : Step(i) PROVE IndInv_Unforg_NoBcast'
                 BY DEF Step, IndInv_Unforg_NoBcast
            <5>2 CASE \E i \in Corr : ReceiveFromAnySender(i) /\ UponV1(i)
                 <6>1 FCConstraints' /\ TypeOK' BY DEF FCConstraints, TypeOK
                 <6>2 sent' = {} /\ pc' = [ j \in Proc |-> "V0" ]
                      <7>1 Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
                           <8>1 ASSUME TypeOK, FCConstraints, sent = {}, pc = [ j \in Proc |-> "V0" ],
                                ReceiveFromAnySender(i)
                                PROVE Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
                                OBVIOUS
                      <7>2 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponV1(i)
                           <8>1 ~UponV1(i) =
                                   \/ ~(pc[i] = "V1") \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                                   \/ ~(sent' = sent \cup { <<i, "ECHO">> }) \/ ~(UNCHANGED << Corr, Faulty >>)
                                OBVIOUS
                           <8>2 pc[i] = "V0"
                                OBVIOUS
                      <7> QED
                 <6> QED
            <5> QED
       <3> QED

IndInvImpliesUnforg ==
  IndInv_Unforg_NoBcast => Unforg
  <1>1 (\A i \in Proc : pc[i] = "V0") => \A i \in Proc : pc[i] # "AC"
       OBVIOUS
  <1>2 IndInv_Unforg_NoBcast => (\A i \in Proc : pc[i] # "AC")
       BY <1>1 DEF IndInv_Unforg_NoBcast
  <1> QED

SpecImpliesUnforg ==
  Spec => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast BY TheoremInitNoBcast
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast' BY NextStep
  <1>3 Spec => []IndInv_Unforg_NoBcast BY PTL DEF Spec
  <1>4 IndInv_Unforg_NoBcast => Unforg BY IndInvImpliesUnforg
  <1> QED

=============================================================================