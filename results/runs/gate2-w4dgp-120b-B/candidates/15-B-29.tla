---- MODULE bcastByz
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
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
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) ==
  /\ Receive(self, TRUE)
  /\ \/ UponV1(self) \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self) \/ UponAcceptSentBefore(self)

Next ==
     \/ \E self \in Corr: Step(self)
     \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

Unforg == (\A i \in Proc : i \in Corr => pc[i] # "AC")
IndInv_Unforg_NoBcast ==
  /\ TypeOK /\ FCConstraints /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

THEOREM NTFRel ==
  N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)
  BY NTF

THEOREM ProcProp == Cardinality(Proc) = N /\ IsFiniteSet(Proc)
  BY FS_Interval, NTFRel

THEOREM UMFS_CardinalityType == \A X, Y, Z :
  /\ IsFiniteSet(X) /\ IsFiniteSet(Y) /\ IsFiniteSet(Z)
  /\ X \cup Y = Z /\ X = Z \ Y
  => Cardinality(X) = Cardinality(Z) - Cardinality(Y)
  <1>1 Cardinality(X) = Cardinality(Z) - Cardinality(Z \cap Y) BY FS_Difference
  <1>2 Z \cap Y = Y OBVIOUS
  <1>3 IsFiniteSet(Z \cap Y) BY FS_Intersection
  <1>4 Cardinality(Z \cap Y) = Cardinality(Y) BY <1>2
  <1> QED BY <1>1, <1>2, <1>3, <1>4

THEOREM FCConstraints_TypeOK_InitNoBcast ==
  InitNoBcast => FCConstraints /\ TypeOK
  <1>1 Corr \subseteq Proc OBVIOUS
  <1>2 Faulty \subseteq Proc OBVIOUS
  <1>3 IsFiniteSet(Corr) BY <1>1, ProcProp, FS_Subset
  <1>4 IsFiniteSet(Faulty) BY <1>2, ProcProp, FS_Subset
  <1>5 Corr \cup Faulty = Proc OBVIOUS
  <1>6 Faulty = Proc \ Corr OBVIOUS
  <1>7 Cardinality(Corr) >= N - T OBVIOUS
  <1>8 Cardinality(Faulty) <= T OBVIOUS
  <1>9 ByzMsgs \subseteq Proc \X M BY <1>2
  <1>10 IsFiniteSet(ByzMsgs)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2> QED BY <2>1, <1>4, FS_Product
  <1>11 Cardinality(ByzMsgs) = Cardinality(Faulty)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2>2 Cardinality(M) = 1 BY FS_Singleton
    <2>3 Cardinality(ByzMsgs) = Cardinality(Faulty) * Cardinality(M)
      BY <2>1, <1>4, FS_Product
    <2>4 QED BY <2>2, <2>3, <1>4, <1>11, FS_CardinalityType
  <1>12 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ] OBVIOUS
  <1>13 Corr \subseteq Proc OBVIOUS
  <1>14 Faulty \subseteq Proc OBVIOUS
  <1>15 sent \subseteq Proc \X M OBVIOUS
  <1>16 rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ] OBVIOUS
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8,
       <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

THEOREM FCConstraints_TypeOK_Init ==
  Init => FCConstraints /\ TypeOK
  <1>1 Corr \subseteq Proc OBVIOUS
  <1>2 Faulty \subseteq Proc OBVIOUS
  <1>3 IsFiniteSet(Corr) BY <1>1, ProcProp, FS_Subset
  <1>4 IsFiniteSet(Faulty) BY <1>2, ProcProp, FS_Subset
  <1>5 Corr \cup Faulty = Proc OBVIOUS
  <1>6 Faulty = Proc \ Corr OBVIOUS
  <1>7 Cardinality(Corr) >= N - T OBVIOUS
  <1>8 Cardinality(Faulty) <= T OBVIOUS
  <1>9 ByzMsgs \subseteq Proc \X M BY <1>2
  <1>10 IsFiniteSet(ByzMsgs)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2> QED BY <2>1, <1>4, FS_Product
  <1>11 Cardinality(ByzMsgs) = Cardinality(Faulty)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2>2 Cardinality(M) = 1 BY FS_Singleton
    <2>3 QED BY <2>2, <2>1, <1>4, FS_Product, FS_CardinalityType
  <1>12 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ] OBVIOUS
  <1>13 Corr \subseteq Proc OBVIOUS
  <1>14 Faulty \subseteq Proc OBVIOUS
  <1>15 sent \subseteq Proc \X M OBVIOUS
  <1>16 rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ] OBVIOUS
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8,
       <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
  BY DEF IndInv_Unforg_NoBcast

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==
  IndInv_Unforg_NoBcast /\ pc = [ i \in Proc |-> "V0" ] => FCConstraints
  <1>1 Corr \subseteq Proc OBVIOUS
  <1>2 Faulty \subseteq Proc OBVIOUS
  <1>3 IsFiniteSet(Corr) BY <1>1, ProcProp, FS_Subset
  <1>4 IsFiniteSet(Faulty) BY <1>2, ProcProp, FS_Subset
  <1>5 Corr \cup Faulty = Proc OBVIOUS
  <1>6 Faulty = Proc \ Corr OBVIOUS
  <1>7 Cardinality(Corr) >= N - T OBVIOUS
  <1>8 Cardinality(Faulty) <= T
    <2>1 Cardinality(Corr) \in Nat BY <1>3, FS_CardinalityType
    <2>2 N - T <= N - F BY NTFRel
    <2>3 QED BY <2>1, <2>2, NTFRel
  <1>9 ByzMsgs \subseteq Proc \X M BY <1>2
  <1>10 IsFiniteSet(ByzMsgs)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2> QED BY <2>1, <1>4, FS_Product
  <1>11 Cardinality(ByzMsgs) = Cardinality(Faulty)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2>2 Cardinality(M) = 1 BY FS_Singleton
    <2>3 QED BY <2>2, <2>1, <1>4, FS_Product, FS_CardinalityType
  <1>12 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ] OBVIOUS
  <1>13 Corr \subseteq Proc OBVIOUS
  <1>14 Faulty \subseteq Proc OBVIOUS
  <1>15 sent \subseteq Proc \X M OBVIOUS
  <1>16 rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ] OBVIOUS
  <1> QED
    BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8,
       <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

THEOREM FCConstraints_TypeOK_Next ==
  FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
  <1>1 FCConstraints' =
       /\ Corr' \subseteq Proc' /\ Faulty' \subseteq Proc'
       /\ IsFiniteSet(Corr') /\ IsFiniteSet(Faulty')
       /\ Corr' \cup Faulty' = Proc' /\ Faulty' = Proc' \ Corr'
       /\ Cardinality(Corr') >= N - T /\ Cardinality(Faulty') <= T
       /\ ByzMsgs' \subseteq Proc' \X M'
       /\ IsFiniteSet(ByzMsgs')
       /\ Cardinality(ByzMsgs') = Cardinality(Faulty')
    BY DEF FCConstraints
  <1>2 TypeOK' =
       /\ sent' \subseteq Proc' \X M'
       /\ pc' \in [ Proc' -> {"V0", "V1", "SE", "AC"} ]
       /\ rcvd' \in [ Proc' -> SUBSET (sent' \cup ByzMsgs') ]
    BY DEF TypeOK
  <1>3 Proc' = Proc BY DEF Proc
  <1>4 Case UNCHANGED vars
    <2>1 Corr' = Corr BY <1>4 DEF vars
    <2>2 Faulty' = Faulty BY <1>4 DEF vars
    <2>3 ByzMsgs' = ByzMsgs BY <2>2 DEF ByzMsgs
    <2>4 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ] BY <1>4 DEFS vars, TypeOK
    <2>5 sent \subseteq sent' BY <1>4 DEF vars
    <2>6 ByzMsgs \subseteq ByzMsgs' BY <1>4, <2>2 DEF ByzMsgs
    <2>7 sent' \subseteq Proc' \X M' BY <1>4 DEFS vars, TypeOK, Proc, M
    <2>8 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
      <3>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <2>5, <2>6
      <3> QED BY <1>4, <3>1 DEFS vars, TypeOK, Receive
    <2> QED BY <1>4, <2>1, <2>3, <2>4, <2>7, <2>8
  <1>5 Case Next
    <2> SUFFICES ASSUME FCConstraints, TypeOK,
        (\E i \in Corr : Step(i)) \/ UNCHANGED vars
        PROVE FCConstraints' /\ TypeOK'
        BY <1>5 DEF Next
    <2>1 CASE \E i \in Corr : Step(i)
      <3> SUFFICES ASSUME FCConstraints, TypeOK, NEW i \in Corr, Step(i)
            PROVE FCConstraints' /\ TypeOK'
            BY <2>1
      <3>1 Step(i) <
        \/ Receive(i, TRUE) /\ UponV1(i)
        \/ Receive(i, TRUE) /\ UponNonFaulty(i)
        \/ Receive(i, TRUE) /\ UponAcceptNotSentBefore(i)
        \/ Receive(i, TRUE) /\ UponAcceptSentBefore(i)
        \/ Receive(i, TRUE) /\ UNCHANGED << pc, sent, Corr, Faulty >>
        BY DEF Step
      <3>2 CASE Receive(i, TRUE) /\ UponV1(i)
        <4>1 FCConstraints' BY <3>2 DEF Receive, UponV1, FCConstraints, ByzMsgs
        <4>2 TypeOK' <
          <5>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
            BY <3>2 DEFS UponV1, TypeOK
          <5>2 sent \subseteq sent' BY <3>2 DEFS UponV1
          <5>3 Faulty' = Faulty BY <3>2 DEFS UponV1
          <5>4 ByzMsgs \subseteq ByzMsgs' BY <3>2, <5>3 DEF ByzMsgs
          <5>5 sent' \subseteq Proc' \X M'
            <6>1 i \in Proc BY <3>2 DEFS TypeOK
            <6>2 << i, "ECHO" >> \in Proc' \X M' BY <6>1 DEFS Proc, M
            <6>3 { << i, "ECHO" >> } \subseteq Proc' \X M' BY <6>2
            <6>4 sent \subseteq Proc' \X M' BY <3>2 DEFS TypeOK, M, Proc
            <6> QED BY <3>2, <6>3, <6>4 DEFS UponV1, TypeOK
          <5>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
            <6>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <5>2, <5>4
            <6>2 Receive(i, TRUE) <=> Receive(i, TRUE) BY DEF Receive
            <6>3 Receive(i, TRUE) <=>
                  (\E newMessages \in SUBSET (sent \cup ByzMsgs) :
                      rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY DEF Receive
            <6> QED BY <3>2, <6>1, <6>2, <6>3 DEFS UponV1, TypeOK, Receive
          <5>7 Corr' = Corr BY <3>2 DEFS UponV1
          <5> QED BY <1>2, <3>2, <4>1, <5>1, <5>5, <5>6, <5>7 DEF TypeOK, FCConstraints
        <4> QED BY <4>1, <4>2
      <3>3 CASE Receive(i, TRUE) /\ UponNonFaulty(i)
        <4>1 FCConstraints' BY <3>3 DEF Receive, UponNonFaulty, FCConstraints, ByzMsgs
        <4>2 TypeOK' <
          <5>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
            BY <3>3 DEFS UponNonFaulty, TypeOK
          <5>2 sent \subseteq sent' BY <3>3 DEFS UponNonFaulty
          <5>3 Faulty' = Faulty BY <3>3 DEFS UponNonFaulty
          <5>4 ByzMsgs \subseteq ByzMsgs' BY <3>3, <5>3 DEF ByzMsgs
          <5>5 sent' \subseteq Proc' \X M'
            <6>1 i \in Proc BY <3>3 DEFS TypeOK
            <6>2 << i, "ECHO" >> \in Proc' \X M' BY <6>1 DEFS Proc, M
            <6>3 { << i, "ECHO" >> } \subseteq Proc' \X M' BY <6>2
            <6>4 sent \subseteq Proc' \X M' BY <3>3 DEFS TypeOK, M, Proc
            <6> QED BY <3>3, <6>3, <6>4 DEFS UponNonFaulty, TypeOK
          <5>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
            <6>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <5>2, <5>4
            <6>2 Receive(i, TRUE) <=> Receive(i, TRUE) BY DEF Receive
            <6>3 Receive(i, TRUE) <=>
                  (\E newMessages \in SUBSET (sent \cup ByzMsgs) :
                      rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY DEF Receive
            <6> QED BY <3>3, <6>1, <6>2, <6>3 DEFS UponNonFaulty, TypeOK, Receive
          <5>7 Corr' = Corr BY <3>3 DEFS UponNonFaulty
          <5> QED BY <1>2, <3>3, <4>1, <5>1, <5>5, <5>6, <5>7 DEF TypeOK, FCConstraints
        <4> QED BY <4>1, <4>2
      <3>4 CASE Receive(i, TRUE) /\ UponAcceptNotSentBefore(i)
        <4>1 FCConstraints' BY <3>4 DEF Receive, UponAcceptNotSentBefore, FCConstraints, ByzMsgs
        <4>2 TypeOK' <
          <5>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
            BY <3>4 DEFS UponAcceptNotSentBefore, TypeOK
          <5>2 sent \subseteq sent' BY <3>4 DEFS UponAcceptNotSentBefore
          <5>3 Faulty' = Faulty BY <3>4 DEFS UponAcceptNotSentBefore
          <5>4 ByzMsgs \subseteq ByzMsgs' BY <3>4, <5>3 DEF ByzMsgs
          <5>5 sent' \subseteq Proc' \X M'
            <6>1 i \in Proc BY <3>4 DEFS TypeOK
            <6>2 << i, "ECHO" >> \in Proc' \X M' BY <6>1 DEFS Proc, M
            <6>3 { << i, "ECHO" >> } \subseteq Proc' \X M' BY <6>2
            <6>4 sent \subseteq Proc' \X M' BY <3>4 DEFS TypeOK, M, Proc
            <6> QED BY <3>4, <6>3, <6>4 DEFS UponAcceptNotSentBefore, TypeOK
          <5>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
            <6>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <5>2, <5>4
            <6>2 Receive(i, TRUE) <=> Receive(i, TRUE) BY DEF Receive
            <6>3 Receive(i, TRUE) <=>
                  (\E newMessages \in SUBSET (sent \cup ByzMsgs) :
                      rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY DEF Receive
            <6> QED BY <3>4, <6>1, <6>2, <6>3 DEFS UponAcceptNotSentBefore, TypeOK, Receive
          <5>7 Corr' = Corr BY <3>4 DEFS UponAcceptNotSentBefore
          <5> QED BY <1>2, <3>4, <4>1, <5>1, <5>5, <5>6, <5>7 DEF TypeOK, FCConstraints
        <4> QED BY <4>1, <4>2
      <3>5 CASE Receive(i, TRUE) /\ UponAcceptSentBefore(i)
        <4>1 FCConstraints' BY <3>5 DEF Receive, UponAcceptSentBefore, FCConstraints, ByzMsgs
        <4>2 TypeOK' <
          <5>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
            BY <3>5 DEFS UponAcceptSentBefore, TypeOK
          <5>2 sent \subseteq sent' BY <3>5 DEFS UponAcceptSentBefore
          <5>3 Faulty' = Faulty BY <3>5 DEFS UponAcceptSentBefore
          <5>4 ByzMsgs \subseteq ByzMsgs' BY <3>5, <5>3 DEF ByzMsgs
          <5>5 sent' \subseteq Proc' \X M'
            <6>1 i \in Proc BY <3>5 DEFS TypeOK
            <6>2 << i, "ECHO" >> \in Proc' \X M' BY <6>1 DEFS Proc, M
            <6>3 { << i, "ECHO" >> } \subseteq Proc' \X M' BY <6>2
            <6>4 sent \subseteq Proc' \X M' BY <3>5 DEFS TypeOK, M, Proc
            <6> QED BY <3>5, <6>3, <6>4 DEFS UponAcceptSentBefore, TypeOK
          <5>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
            <6>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <5>2, <5>4
            <6>2 Receive(i, TRUE) <=> Receive(i, TRUE) BY DEF Receive
            <6>3 Receive(i, TRUE) <=>
                  (\E newMessages \in SUBSET (sent \cup ByzMsgs) :
                      rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY DEF Receive
            <6> QED BY <3>5, <6>1, <6>2, <6>3 DEFS UponAcceptSentBefore, TypeOK, Receive
          <5>7 Corr' = Corr BY <3>5 DEFS UponAcceptSentBefore
          <5> QED BY <1>2, <3>5, <4>1, <5>1, <5>5, <5>6, <5>7 DEF TypeOK, FCConstraints
        <4> QED BY <4>1, <4>2
      <3>6 CASE Receive(i, TRUE) /\ UNCHANGED << pc, sent, Corr, Faulty >>
        <4>1 FCConstraints' BY <3>6 DEF FCConstraints, ByzMsgs
        <4>2 TypeOK' <
          <5>1 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ] BY <3>6 DEFS vars, TypeOK
          <5>2 sent \subseteq sent' BY <3>6
          <5>3 Faulty' = Faulty BY <3>6
          <5>4 ByzMsgs \subseteq ByzMsgs' BY <3>6, <5>3 DEF ByzMsgs
          <5>5 sent' \subseteq Proc' \X M' BY <3>6 DEFS vars, TypeOK, Proc, M
          <5>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
            <6>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <5>2, <5>4
            <6>2 Receive(i, TRUE) <=> Receive(i, TRUE) BY DEF Receive
            <6>3 Receive(i, TRUE) <=>
                  (\E newMessages \in SUBSET (sent \cup ByzMsgs) :
                      rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY DEF Receive
            <6> QED BY <3>6, <6>1, <6>2, <6>3 DEFS vars, TypeOK, Receive
          <5>7 Corr' = Corr BY <3>6 DEFS vars
          <5> QED BY <1>2, <3>6, <3>1, <4>1, <5>5, <5>6 DEF TypeOK, FCConstraints
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Step
    <2>2 CASE UNCHANGED vars
      <3> SUFFICES ASSUME FCConstraints, TypeOK, UNCHANGED vars
            PROVE FCConstraints' /\ TypeOK' BY <2>2
      <3> QED BY <1>5
    <2> QED BY <1>5, <2>1, <2>2
  <1> QED BY <1>5, <1>6, PTL

THEOREM FCConstraints_TypeOK_SpecNoBcast ==
  SpecNoBcast => [](FCConstraints /\ TypeOK)
  <1>1 InitNoBcast => FCConstraints /\ TypeOK BY FCConstraints_TypeOK_InitNoBcast
  <1>2 FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK' BY FCConstraints_TypeOK_Next
  <1> QED BY <1>1, <1>2, PTL

THEOREM Unforg_Step1 == InitNoBcast => IndInv_Unforg_NoBcast
  <1>1 InitNoBcast => FCConstraints /\ TypeOK BY FCConstraints_TypeOK_InitNoBcast
  <1>2 InitNoBcast => sent = {} OBVIOUS
  <1>3 InitNoBcast => pc = [ i \in Proc |-> "V0" ] OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3

THEOREM Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1>1 IndInv_Unforg_NoBcast' = /\ TypeOK' /\ FCConstraints'
        /\ sent' = {} /\ pc' = [ i \in Proc |-> "V0" ] BY DEF IndInv_Unforg_NoBcast
  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
    <2>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => FCConstraints' /\ TypeOK'
      BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
    <2>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => sent' = {} /\ pc' = [ i \in Proc |-> "V0" ]
      BY DEF IndInv_Unforg_NoBcast, vars
    <2> QED BY <2>1, <2>2
  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
    <2>1 CASE UNCHANGED vars
      <3>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast' BY <2>1
      <3> QED BY <1>2
    <2>2 CASE (\E i \in Corr : Step(i))
      <3>1 IndInv_Unforg_NoBcast /\ (\E i \in Corr : Step(i)) => IndInv_Unforg_NoBcast'
        <4>1 CASE (\E i \in Corr : Step(i))
          <5>1 IndInv_Unforg_NoBcast /\ Step(i) => IndInv_Unforg_NoBcast'
            <6>1 FCConstraints' /\ TypeOK' BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
            <6>2 sent' = {} /\ pc' = [ i \in Proc |-> "V0" ]
              <7>1 Step(i) <=>
                    \/ Receive(i, TRUE) /\ UponV1(i)
                    \/ Receive(i, TRUE) /\ UponNonFaulty(i)
                    \/ Receive(i, TRUE) /\ UponAcceptNotSentBefore(i)
                    \/ Receive(i, TRUE) /\ UponAcceptSentBefore(i) 
                    \/ Receive(i, TRUE) /\ UNCHANGED << pc, sent, Corr, Faulty >>
                BY DEF Step
              <7>2 IndInv_Unforg_NoBcast /\ Receive(i, TRUE) => 
                    Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
                <8>1 Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
                  <9>1 Receive(i, TRUE) => Cardinality(rcvd'[i]) <= T
                    <10>1 T < N - 2 * T BY NTFRel
                    <10>2 Cardinality(rcvd'[i]) \in Nat BY <7>2
                    <10>3 Cardinality(rcvd'[i]) < N - 2 * T BY <7>2, <10>1, <10>2, NTFRel
                    <10> QED BY NTFRel, <7>2 <10>3
                  <9>2 Cardinality(rcvd'[i]) \in Nat
                    BY <7>2, FS_CardinalityType DEF IndInv_Unforg_NoBcast
                  <9> QED BY <9>1, <9>2
                <8> QED BY <8>1
              <7>3 CASE Receive(i, TRUE) /\ UNCHANGED << pc, sent, Corr, Faulty >>
                BY <7>3 DEF IndInv_Unforg_NoBcast
              <7>4 CASE Receive(i, TRUE) /\ ~UponV1(i)
                <8>1 Receive(i, TRUE) => ~UponV1(i) BY <7>4 DEF IndInv_Unforg_NoBcast
                <8>2 ~UponV1(i) = \/ ~(pc[i] = "V1") \/ ~(pc' = [ pc EXCEPT ![i] = "SE" ])
                                 \/ ~(sent' = sent \cup { <<i, "ECHO">> })
                                 \/ ~(UNCHANGED << Corr, Faulty >>)
                  BY DEF UponV1
                <8>3 pc[i] = "V0"
                  <9>1 i \in Corr OBVIOUS
                  <9>2 i \in Proc BY DEF IndInv_Unforg_NoBcast, FCConstraints
                  <9> QED BY <9>2
                <8> QED BY <8>1, <8>2, <8>3
              <7>5 CASE Receive(i, TRUE) /\ ~UponNonFaulty(i)
                <8>1 Receive(i, TRUE) => ~UponNonFaulty(i) BY <7>5 DEF IndInv_Unforg_NoBcast
                <8>2 ~UponNonFaulty(i) = \/ ~(pc[i] \in { "V0", "V1" })
                                      \/ ~(Cardinality(rcvd'[i]) >= N - 2 * T)
                                      \/ ~(Cardinality(rcvd'[i]) < N - T)
                                      \/ ~(pc' = [ pc EXCEPT ![i] = "SE" ])
                                      \/ ~(sent' = sent \cup { <<i, "ECHO">> })
                                      \/ ~(UNCHANGED << Corr, Faulty >>)
                  BY DEF UponNonFaulty
                <8>3 (Cardinality(rcvd'[i]) <= T) => ~UponNonFaulty(i)
                  <9>1 T < N - 2 * T BY NTFRel
                  <9>2 Cardinality(rcvd'[i]) \in Nat BY <7>2
                  <9>3 Cardinality(rcvd'[i]) < N - 2 * T BY <7>2, <9>1, <9>2, NTFRel
                  <9>4 Cardinality(rcvd'[i]) < N - T BY <7>2, <9>3, NTFRel
                  <9> QED BY <7>2, <8>1, <9>1, <9>2, <9>4
                <8> QED BY <7>2, <8>1, <8>3
              <7>6 CASE Receive(i, TRUE) /\ ~UponAcceptNotSentBefore(i)
                <8>1 Receive(i, TRUE) => ~UponAcceptNotSentBefore(i) BY <7>6 DEF IndInv_Unforg_NoBcast
                <8>2 ~UponAcceptNotSentBefore(i) = \/ ~(pc[i] \in { "V0", "V1" })
                                      \/ ~(Cardinality(rcvd'[i]) >= N - T)
                                      \/ ~(pc' = [ pc EXCEPT ![i] = "AC" ])
                                      \/ ~(sent' = sent \cup { <<i, "ECHO">> })
                                      \/ ~(UNCHANGED << Corr, Faulty >>)
                  BY DEF UponAcceptNotSentBefore
                <8>3 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptNotSentBefore(i)
                  <9>1 T < N - 2 * T BY NTFRel
                  <9>2 Cardinality(rcvd'[i]) \in Nat BY <7>2
                  <9>3 Cardinality(rcvd'[i]) < N - 2 * T BY <7>2, <9>1, <9>2, NTFRel
                  <9>4 Cardinality(rcvd'[i]) < N - T BY <7>2, <9>3, NTFRel
                  <9> QED BY <7>2, <8>1, <9>1, <9>2, <9>4
                <8> QED BY <7>2, <8>1, <8>3
              <7>7 CASE Receive(i, TRUE) /\ ~UponAcceptSentBefore(i)
                <8>1 Receive(i, TRUE) => ~UponAcceptSentBefore(i) BY <7>7 DEF IndInv_Unforg_NoBcast
                <8>2 ~UponAcceptSentBefore(i) = \/ ~(pc[i] = "SE")
                                      \/ ~(Cardinality(rcvd'[i]) >= N - T)
                                      \/ ~(pc' = [ pc EXCEPT ![i] = "AC" ])
                                      \/ ~(sent' = sent)
                                      \/ ~(UNCHANGED << Corr, Faulty >>)
                  BY DEF UponAcceptSentBefore
                <8>3 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptSentBefore(i)
                  <9>1 T < N - 2 * T BY NTFRel
                  <9>2 Cardinality(rcvd'[i]) \in Nat BY <7>2
                  <9>3 Cardinality(rcvd'[i]) < N - 2 * T BY <7>2, <9>1, <9>2, NTFRel
                  <9>4 Cardinality(rcvd'[i]) < N - T BY <7>2, <9>3, NTFRel
                  <9> QED BY <7>2, <8>1, <9>1, <9>2, <9>4
                <8> QED BY <7>2, <8>1, <8>3
              <7> QED BY <7>1, <7>3, <7>4, <7>5, <7>6, <7>7
            <5> QED BY <5>1, <5>2, <5>3, <5>4, <5>5, <5>6
          <4> QED BY <4>1, <4>2, <4>3
        <3> QED BY <3>1, <3>2
      <2> QED BY <2>1, <2>2
    <1> QED BY <1>2, <1>3

THEOREM Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
  <1>1 (\A i \in Proc : pc[i] = "V0") => \A i \in Proc : pc[i] # "AC" OBVIOUS
  <1>2 Unforg QED BY <1>1 DEF Unforg

THEOREM Unforg_Step4 == SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast BY Unforg_Step1
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast' BY Unforg_Step2
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast BY <1>1, <1>2, PTL
  <1>4 IndInv_Unforg_NoBcast => Unforg BY Unforg_Step3
  <1> QED BY <1>3, <1>4, PTL

=============================================================================