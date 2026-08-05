------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
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

SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

CorrLtl == (\A i \in Corr: pc[i] = "V1") => <> (\A i \in Corr: pc[i] = "AC")
RelayLtl == [] ((\E i \in Corr: pc[i] = "AC") => <> (\A i \in Corr: pc[i] = "AC"))
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [] (\A i \in Corr: pc[i] /= "AC")
Unforg == (\A i \in Proc: i \in Corr => (pc[i] /= "AC"))

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

IndInv_Unforg_NoBcast_TLC ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] # "AC"
  /\ sent = {}
  /\ rcvd \in [ Proc -> SUBSET ByzMsgs ]

THEOREM FCConstraints_TypeOK_InitNoBcast ==
  InitNoBcast => FCConstraints /\ TypeOK
  BY <1>1 DEF InitNoBcast, Init, FCConstraints, TypeOK

THEOREM FCConstraints_TypeOK_Init ==
  Init => FCConstraints /\ TypeOK
  BY <1>1 DEF Init, FCConstraints, TypeOK

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
  BY DEF IndInv_Unforg_NoBcast

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==
  IndInv_Unforg_NoBcast_TLC => FCConstraints
  BY <1>1 DEF IndInv_Unforg_NoBcast_TLC, FCConstraints

THEOREM FCConstraints_TypeOK_Next ==
  FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
  BY <2>1 DEF FCConstraints, TypeOK, Next

THEOREM FCConstraints_TypeOK_SpecNoBcast == SpecNoBcast => [](FCConstraints /\ TypeOK)
  BY <1>1, <1>2, PTL DEF SpecNoBcast

THEOREM Unforg_Step1 == InitNoBcast => IndInv_Unforg_NoBcast
  BY <1>1, <1>2, <1>3 DEF InitNoBcast, Init, IndInv_Unforg_NoBcast

THEOREM Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1>1 IndInv_Unforg_NoBcast' = (TypeOK' /\ FCConstraints' /\ sent' = {} /\ pc' = [j \in Proc |-> "V0"])
       BY DEF IndInv_Unforg_NoBcast

  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
       BY <2>1 DEF IndInv_Unforg_NoBcast, vars

  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
       <2>1 CASE UNCHANGED vars
            <3>1 UNCHANGED vars => IndInv_Unforg_NoBcast' BY <2>1
            <3> QED BY <1>2

            <3>2 CASE \E i \in Corr: Step(i)
                 <4>1 \E i \in Corr: Step(i) => IndInv_Unforg_NoBcast'
                      <5>1 Step(i) <=>
                         \/ ReceiveFromAnySender(i) /\ UponV1(i)
                         \/ ReceiveFromAnySender(i) /\ UponNonFaulty(i)
                         \/ ReceiveFromAnySender(i) /\ UponAcceptNotSentBefore(i)
                         \/ ReceiveFromAnySender(i) /\ UponAcceptSentBefore(i)
                         \/ ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
                            BY DEF Step

                      <5>2 FCConstraints' /\ TypeOK' BY <4>1, FCConstraints_TypeOK_Next, DEF IndInv_Unforg_NoBcast

                      <5>3 (sent' = {} /\ pc' = [j \in Proc |-> "V0"])
                         <6>1 ~UponV1(i)
                            <7>1 ~UponV1(i) = \/ pc[i] # "V1" \/ pc' # [pc EXCEPT ![i] = "SE"]
                                   \/ sent' # sent \cup {<<i, "ECHO">>} \/ UNCHANGED <<Corr, Faulty>>
                                BY DEF UponV1
                            <7>2 pc[i] = "V0"
                                <8>1 (i \in Corr) BY <1>3
                                <8>2 (i \in Proc) BY <1>3
                                <8> QED BY <8>1
                            <7> QED BY <7>1, <7>2
                         <6>2 ~UponNonFaulty(i)
                            <7>1 ~UponNonFaulty(i) = \/ pc[i] \in {"V0", "V1"} \/ Cardinality(rcvd'[i]) < N - 2*T
                                   \/ Cardinality(rcvd'[i]) >= N - T \/ pc' # [pc EXCEPT ![i] = "SE"]
                                   \/ sent' # sent \cup {<<i, "ECHO">>} \/ UNCHANGED <<Corr, Faulty>>
                                BY DEF UponNonFaulty
                            <7>2 (Cardinality(rcvd'[i]) <= T) => ~UponNonFaulty(i)
                                <8>1 T < N - 2*T BY <1>2
                                <8>2 Cardinality(rcvd'[i]) \in Nat BY <5>3
                                <8>3 Cardinality(rcvd'[i]) < N - 2*T BY <5>3, <8>1, <8>2, <1>2
                                <8> QED BY <7>1, <8>1, <8>2, <8>3, <1>2
                            <7> QED BY <6>1, <5>3
                         <6>3 ~UponAcceptNotSentBefore(i)
                            <7>1 ~UponAcceptNotSentBefore(i) = \/ pc[i] \in {"V0", "V1"} \/ Cardinality(rcvd'[i]) < N - T
                                   \/ pc' # [pc EXCEPT ![i] = "AC"] \/ sent' # sent \cup {<<i, "ECHO">>} \/ UNCHANGED <<Corr, Faulty>>
                                BY DEF UponAcceptNotSentBefore
                            <7>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptNotSentBefore(i)
                                <8>1 T < N - 2*T BY <1>2
                                <8>2 Cardinality(rcvd'[i]) \in Nat BY <5>3
                                <8>3 Cardinality(rcvd'[i]) < N - 2*T BY <5>3, <8>1, <8>2, <1>2
                                <8>4 Cardinality(rcvd'[i]) < N - T BY <5>3, <8>3, <1>2
                                <8> QED BY <7>1, <8>1, <8>2, <8>4, <1>2
                            <7> QED BY <6>2, <5>3
                         <6>4 ~UponAcceptSentBefore(i)
                            <7>1 ~UponAcceptSentBefore(i) = \/ pc[i] # "SE" \/ Cardinality(rcvd'[i]) < N - T
                                   \/ pc' # [pc EXCEPT ![i] = "AC"] \/ sent' # sent \/ UNCHANGED <<Corr, Faulty>>
                                BY DEF UponAcceptSentBefore
                            <7>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptSentBefore(i)
                                <8>1 T < N - 2*T BY <1>2
                                <8>2 Cardinality(rcvd'[i]) \in Nat BY <5>3
                                <8>3 Cardinality(rcvd'[i]) < N - 2*T BY <5>3, <8>1, <8>2, <1>2
                                <8>4 Cardinality(rcvd'[i]) < N - T BY <5>3, <8>3, <1>2
                                <8> QED BY <7>1, <8>1, <8>2, <8>4, <1>2
                            <7> QED BY <6>3, <5>3
                         <6>5 ~ReceiveFromAnySender(i)
                            <7>1 ReceiveFromAnySender(i) => (Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat)
                                BY <5>3, <2>1, <1>2
                            <7> QED BY <6>1, <5>3, <1>2
                         <6> QED BY <6>1, <6>2, <6>3, <6>4, <6>5, <5>2, <1>2
                      <5> QED BY <5>1, <5>2, <5>3, <4>1
                 <4> QED BY <4>1, FCConstraints_TypeOK_Next, <1>2, <1>3
            <2> QED BY <1>1, <1>2, <1>3

THEOREM Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
  <1>1 pc = [i \in Proc |-> "V0"] => \A i \in Proc : pc[i] # "AC" OBVIOUS
  <1>2 (TypeOK /\ pc = [i \in Proc |-> "V0"]) => \A i \in Proc : pc[i] # "AC" BY <1>1
  <1>3 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0"]) => \A i \in Proc : pc[i] # "AC" BY <1>2
  <1>4 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0"] /\ sent = {}) => \A i \in Proc : pc[i] # "AC" BY <1>3
  <1>5 IndInv_Unforg_NoBcast => \A i \in Proc : pc[i] # "AC" BY <1>4
  <1>6 QED BY <1>5

THEOREM Unforg_Step4 == SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast BY Unforg_Step1
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast' BY Unforg_Step2
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast BY <1>1, <1>2, PTL DEF SpecNoBcast
  <1>4 IndInv_Unforg_NoBcast => Unforg BY Unforg_Step3
  <1> QED BY <1>3, <1>4, PTL

=============================================================================