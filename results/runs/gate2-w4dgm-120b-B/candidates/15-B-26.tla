------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
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
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {} ) ) :
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

Spec == Init /\ [][Next]_vars
             /\ WF_vars(\E self \in Corr: /\ ReceiveFromCorrectSender(self)
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

Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC"))
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] /= "AC")

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

THEOREM Unforg_Step1 == InitNoBcast => IndInv_Unforg_NoBcast
  <1>1 InitNoBcast => FCConstraints /\ TypeOK
    BY (FCConstraints_TypeOK_InitNoBcast)
  <1>2 InitNoBcast => sent = {}
    OBVIOUS
  <1>3 InitNoBcast => pc = [ i \in Proc |-> "V0" ]
    OBVIOUS
  <1> QED

THEOREM Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1>1 IndInv_Unforg_NoBcast' = / TypeOK' /\ FCConstraints' /\ sent' = {} /\ pc' = [i \in Proc' |-> "V0"]
      BY DEF IndInv_Unforg_NoBcast

  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
    <2>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => FCConstraints' /\ TypeOK'
      BY (FCConstraints_TypeOK_Next) DEF IndInv_Unforg_NoBcast
    <2>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => (sent' = {} /\ pc' = [ j \in Proc |-> "V0" ])
      BY DEF IndInv_Unforg_NoBcast, vars
    <2> QED
      BY <2>1, <2>2 DEF IndInv_Unforg_NoBcast, vars
  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
    <2> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [ i \in Proc |-> "V0" ], (\E i \in Corr : Step(i)) \/ UNCHANGED vars
                  PROVE IndInv_Unforg_NoBcast'
      OBVIOUS
    <2>1 CASE UNCHANGED vars
      <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [ i \in Proc |-> "V0" ], UNCHANGED vars
                   PROVE IndInv_Unforg_NoBcast'
          OBVIOUS
      <3> QED
        BY <1>2
    <2>2 CASE (\E i \in Corr : Step(i))
      <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [ i \in Proc |-> "V0"], NEW i \in Corr, Step(i)
                   PROVE IndInv_Unforg_NoBcast'
          OBVIOUS
      <3>1 FCConstraints' /\ TypeOK'
        BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
      <3>2 sent' = {} /\ pc' = [ j \in Proc |-> "V0" ]
        <4>1 Step(i) <=>
                \/ ReceiveFromAnySender(i) /\ UponV1(i)
                \/ ReceiveFromAnySender(i) /\ UponNonFaulty(i)
                \/ ReceiveFromAnySender(i) /\ UponAcceptNotSentBefore(i)
                \/ ReceiveFromAnySender(i) /\ UponAcceptSentBefore(i)
                \/ ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
          BY DEF Step
        <4>2 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
          <5>1 sent = {}
            OBVIOUS
          <5>2 sent \cup ByzMsgs = ByzMsgs
            OBVIOUS
          <5>3 rcvd[i] \subseteq ByzMsgs
            BY <5>2, DEF TypeOK
          <5>4 rcvd'[i] \subseteq ByzMsgs
            <6>1 ReceiveFromAnySender(i) <=> Receive(i, TRUE)
              BY DEF ReceiveFromAnySender
            <6>2 Receive(i, TRUE) <=>
                    (\E newMessages \in SUBSET ByzMsgs : rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY <5>1, <6>1, DEF Receive
            <6>3 Receive(i, TRUE)
              BY <6>1
            <6>4 \E newMessages \in SUBSET ByzMsgs : rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ]
              BY <6>2, <6>3
            <6>5 rcvd'[i] \subseteq (rcvd[i] \cup ByzMsgs)
              <7>1 PICK newMessages \in SUBSET ByzMsgs : rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ]
                BY <6>4
              <7>2 rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ]
                BY <7>1
              <7>3 rcvd'[i] = rcvd[i] \cup newMessages
                BY <7>2
              <7>4 QED
                BY <5>3, <7>3
            <6> QED
              BY <5>3, <6>5, DEF Receive
          <5>5 Cardinality(Faulty) <= T
            BY DEF FCConstraints
          <5>6 Cardinality(ByzMsgs) = Cardinality(Faulty)
            BY DEF FCConstraints
          <5>7 Cardinality(ByzMsgs) <= T
            BY <5>5, <5>6
          <5>8 Cardinality(rcvd'[i]) <= Cardinality(ByzMsgs)
            <6>1 rcvd'[i] \in SUBSET ByzMsgs
              BY <5>4
            <6>2 Cardinality(rcvd'[i]) <= T
              BY <5>7, FS_CardinalityType
            <6> QED
              BY <6>1, FS_Subset
          <5>9 Cardinality(ByzMsgs) \in Nat
            BY FS_CardinalityType DEF FCConstraints
          <5>10 IsFiniteSet(rcvd'[i])
            <6>1 rcvd'[i] \in SUBSET ByzMsgs
              BY <5>4
            <6> QED
              BY <6>1, FS_Subset DEF FCConstraints
          <5>11 Cardinality(rcvd'[i]) \in Nat
            BY <5>10, FS_CardinalityType
          <5> QED
            BY <5>11, <5>9, <5>7, <5>8, NTFRel
        <4>3 CASE ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
          BY <4>1 DEF IndInv_Unforg_NoBcast
        <4>4 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponV1(i)
          <5>1 ~UponV1(i) = \/ ~(pc[i] = "V1") \/ ~(pc' = [pc EXCEPT ![i] = "SE"]) \/ ~(sent' = sent \cup { <<i, "ECHO">> }) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponV1
          <5>2 pc[i] = "V0"
            <6>1 i \in Corr
              OBVIOUS
            <6>2 i \in Proc
              BY DEF IndInv_Unforg_NoBcast, FCConstraints
            <6> QED
              BY <6>2
          <5> QED
            BY <5>1, <5>2
        <4>5 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponNonFaulty(i)
          <5>1 ~UponNonFaulty(i) =
                  \/ ~(pc[i] \in { "V0", "V1" }) \/ ~(Cardinality(rcvd'[i]) >= N - 2 * T)
                  \/ ~(Cardinality(rcvd'[i]) < N - T) \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                  \/ ~(sent' = sent \cup { <<i, "ECHO">> }) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponNonFaulty
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponNonFaulty(i)
            <6>1 T < N - 2 * T
              BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat
              BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2 * T
              BY <4>2, <6>1, <6>2, NTFRel
            <6> QED
              BY <5>1, NTFRel, <6>2, <6>3 DEF UponNonFaulty
          <5> QED
            BY <4>2, <5>2
        <4>6 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptNotSentBefore(i)
          <5>1 ~UponAcceptNotSentBefore(i) =
                  \/ ~(pc[i] \in { "V0", "V1" }) \/ ~(Cardinality(rcvd'[i]) >= N - T)
                  \/ ~(pc' = [pc EXCEPT ![i] = "AC"]) \/ ~(sent' = sent \cup { <<i, "ECHO">> }) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponAcceptNotSentBefore
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptNotSentBefore(i)
            <6>1 T < N - 2 * T
              BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat
              BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2 * T
              BY <4>2, <6>1, <6>2, NTFRel
            <6>4 Cardinality(rcvd'[i]) < N - T
              BY <4>2, <6>3, NTFRel
            <6> QED
              BY <5>1, NTFRel, <6>2, <6>4 DEF UponAcceptNotSentBefore
          <5> QED
            BY <4>2, <5>2
        <4>7 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptSentBefore(i)
          <5>1 ~UponAcceptSentBefore(i) =
                  \/ ~(pc[i] = "SE") \/ ~(Cardinality(rcvd'[i]) >= N - T)
                  \/ ~(pc' = [pc EXCEPT ![i] = "AC"]) \/ ~(sent' = sent) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponAcceptSentBefore
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptSentBefore(i)
            <6>1 T < N - 2 * T
              BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat
              BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2 * T
              BY <4>2, <6>1, <6>2, NTFRel
            <6>4 Cardinality(rcvd'[i]) < N - T
              BY <4>2, <6>3, NTFRel
            <6> QED
              BY <5>1, NTFRel, <6>2, <6>4 DEF UponAcceptSentBefore
          <5> QED
            BY <4>2, <5>2
        <4> QED
          BY <4>1, <4>3, <4>4, <4>5, <4>6, <4>7
      <3> QED
        BY <3>1, <3>2 DEF IndInv_Unforg_NoBcast
    <2> QED
      BY <2>1, <2>2 DEF IndInv_Unforg_NoBcast
  <1> QED
    BY <1>1, <1>2, <1>3

THEOREM Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
  <1>1 pc = [ i \in Proc |-> "V0" ] => \A i \in Proc : pc[i] # "AC"
    OBVIOUS
  <1>2 (TypeOK /\ pc = [ i \in Proc |-> "V0" ]) => \A i \in Proc : pc[i] # "AC"
    BY <1>1
  <1>3 (TypeOK /\ FCConstraints /\ pc = [ i \in Proc |-> "V0" ]) => \A i \in Proc : pc[i] # "AC"
    BY <1>2
  <1>4 (TypeOK /\ FCConstraints /\ pc = [ i \in Proc |-> "V0" ] /\ sent = {}) => \A i \in Proc : pc[i] # "AC"
    BY <1>3
  <1>5 IndInv_Unforg_NoBcast => \A i \in Proc : pc[i] # "AC"
    BY <1>4 DEF IndInv_Unforg_NoBcast
  <1>6 IndInv_Unforg_NoBcast => \A i \in Proc : i \in Corr => pc[i] # "AC"
    BY <1>5
  <1> QED
    BY <1>6 DEF Unforg

THEOREM Unforg_Step4 == SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast
    BY Unforg_Step1
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
    BY Unforg_Step2
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast
    BY <1>1, <1>2, PTL DEF SpecNoBcast
  <1>4 IndInv_Unforg_NoBcast => Unforg
    BY Unforg_Step3
  <1> QED
    BY <1>3, <1>4, PTL

=============================================================================