------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F
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
\* A correct process can receive a subset of sent and a subset of ByzMsgs.
Receive(self, includeByz) == \E newMsgs \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
        rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMsgs ]

ReceiveFromCorrect(self) == Receive(self, FALSE)
ReceiveFromAny(self) == Receive(self, TRUE)
UponV1(self) == /\ pc[self] = "V1"
               /\ pc' = [ pc EXCEPT ![self] = "SE" ]
               /\ sent' = sent \cup { <<self, "ECHO">> }
               /\ UNCHANGED << Corr, Faulty >>
UponNonFaulty(self) == /\ pc[self] \notin { "V0", "V1" }
                       /\ Cardinality(rcvd'[self]) >= N - 2*T
                       /\ Cardinality(rcvd'[self]) < N - T
                       /\ pc' = [ pc EXCEPT ![self] = "SE" ]
                       /\ sent' = sent \cup { <<self, "ECHO">> }
                       /\ UNCHANGED << Corr, Faulty >>
UponAcceptNotSent(self) == /\ pc[self] \in { "V0", "V1" }
                           /\ Cardinality(rcvd'[self]) >= N - T
                           /\ pc' = [ pc EXCEPT ![self] = "AC" ]
                           /\ sent' = sent \cup { <<self, "ECHO">> }
                           /\ UNCHANGED << Corr, Faulty >>
UponAcceptSent(self) == /\ pc[self] = "SE"
                         /\ Cardinality(rcvd'[self]) >= N - T
                         /\ pc' = [ pc EXCEPT ![self] = "AC" ]
                         /\ sent' = sent
                         /\ UNCHANGED << Corr, Faulty >>

Step(self) == ReceiveFromAny(self) /\ (UponV1(self) \/ UponNonFaulty(self)
                                      \/ UponAcceptNotSent(self) \/ UponAcceptSent(self))
Next == (\E self \in Corr : Step(self)) \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

FCConstraints == /\ Corr \cup Faulty = Proc
                 /\ Faulty = Proc \ Corr
                 /\ Cardinality(Corr) >= N - T
                 /\ Cardinality(Faulty) <= T
                 /\ ByzMsgs \subseteq Proc \X M
                 /\ IsFiniteSet(ByzMsgs)
                 /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC"))

TypeOK == /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
          /\ Corr \subseteq Proc
          /\ Faulty \subseteq Proc
          /\ sent \subseteq Proc \X M
          /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

UMFS_Cardinality == \A X, Y, Z : /\ IsFiniteSet(X) /\ IsFiniteSet(Y) /\ IsFiniteSet(Z)
                                 /\ X \cup Y = Z /\ X = Z \ Y
                    => Cardinality(X) = Cardinality(Z) - Cardinality(Y)

IndInv_Unforg == /\ TypeOK
                 /\ FCConstraints
                 /\ sent = {}
                 /\ pc = [ i \in Proc |-> "V0" ]

IndInv_Unforg_TLC == /\ pc = [ i \in Proc |-> "V0" ]
                     /\ Corr \in SUBSET Proc
                     /\ Cardinality(Corr) >= N - T
                     /\ Faulty = Proc \ Corr
                     /\ (\A i \in Proc : pc[i] # "AC")
                     /\ sent = {}
                     /\ rcvd \in [ Proc -> sent \cup SUBSET ByzMsgs ]

THEOREM FCConstraints_TypeOK_InitNoBcast == InitNoBcast => FCConstraints /\ TypeOK
    BY DEF InitNoBcast, Init, FCConstraints, TypeOK

THEOREM FCConstraints_TypeOK_Init == Init => FCConstraints /\ TypeOK
    BY DEF Init, FCConstraints, TypeOK

THEOREM FCConstraints_TypeOK_IndInv_Unforg == IndInv_Unforg => FCConstraints /\ TypeOK
    BY DEF IndInv_Unforg

THEOREM FCConstraints_TypeOK_IndInv_Unforg_TLC ==
    IndInv_Unforg_TLC => FCConstraints
    BY DEF IndInv_Unforg_TLC, FCConstraints

THEOREM FCConstraints_TypeOK_Next ==
    FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
    BY DEF FCConstraints, TypeOK, Next, vars

THEOREM FCConstraints_TypeOK_SpecNoBcast ==
    SpecNoBcast => [](FCConstraints /\ TypeOK)
    BY FCConstraints_TypeOK_InitNoBcast, FCConstraints_TypeOK_Next,
       PTL DEF SpecNoBcast

THEOREM Unforg_Step1 == InitNoBcast => IndInv_Unforg
    BY FCConstraints_TypeOK_InitNoBcast, DEF InitNoBcast, Init, IndInv_Unforg

THEOREM Unforg_Step2 == IndInv_Unforg /\ [Next]_vars => IndInv_Unforg'
    BY DEF IndInv_Unforg, Next, vars

THEOREM Unforg_Step3 == IndInv_Unforg => Unforg
    BY DEF IndInv_Unforg, Unforg

THEOREM Unforg_Step4 == SpecNoBcast => []Unforg
    BY Unforg_Step1, Unforg_Step2, Unforg_Step3,
       PTL DEF SpecNoBcast

=============================================================================