------------------------------ MODULE bcastByz ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast distributed
   algorithm with Byzantine faults.

   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94

   A short description of the parameterized model is described in:
   Gmeiner, Annu, et al. "Tutorial on parameterized model checking of fault-
   tolerant distributed algorithms." International School on Formal Methods for
   the Design of Computer, Communication and Software Systems. Springer
   International Publishing, 2014.

   This specification has a TLAPS proof for property Unforgeability: if process p is
   correct and does not broadcast a message m, then no correct process ever accepts
   m. The formula InitNoBcast represents that the transmitter does not broadcast any
   message. So, we prove (InitNoBcast /\ [][Next]_vars) => []Unforg.

   We can use TLC to check two properties (for fixed parameters N, T, F):
    - Correctness: if a correct process broadcasts, then every correct process accepts,
    - Replay: if a correct process accepts, then every correct process accepts.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

   This file is subject to the license bundled with this package; see the file LICENSE.
 *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

(* Instead of a broadcaster, two initial values V0 and V1 at correct processes model
   whether a process has received the INIT message from the broadcaster. The
   precondition of correctness is that all correct processes initially have V1;
   the precondition of unforgeability is that all correct processes initially have V0.
 *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* The special case: all correct processes initially have the value V0. *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* A correct process receives all ECHO messages from other correct processes (a subset of
   sent) and a subset of all possible ECHO messages from Byzantine processes (a subset of
   ByzMsgs). If includeByz is FALSE the Byzantine messages are not included. *)
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup newMessages ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self) == Receive(self, TRUE)

(* The first if-then in Fig. 7: if process p received an INIT message and did not
   send <ECHO> before, it sends <ECHO> to all. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* The third if-then in Fig. 7: if correct process p received <ECHO> from at least N-2T
   distinct processes and did not send <ECHO> before, it sends <ECHO> to all. *)
UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* The second and third if-then in Fig. 7: if process p received <ECHO> from at least
   N-T distinct processes and did not send before, it accepts and sends <ECHO>. *)
UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* The second if-then in Fig. 7: if process p sent <ECHO> and received <ECHO> from at
   least N-T distinct processes, it accepts. *)
UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED << sent, Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ (UponV1(self) \/ UponNonFaulty(self) \/ UponAcceptNotSentBefore(self) \/ UponAcceptSentBefore(self))
  /\ UNCHANGED << Corr, Faulty >>

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

FCConstraints ==
  /\ Corr \cup Faulty = Proc /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\A i \in Corr: pc[i] = "AC")
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] # "AC")
Unforg == (\A i \in Proc: i \in Corr => (pc[i] # "AC"))

(* No correct process broadcasts any ECHO message. *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

(* A version of IndInv_Unforg_NoBcast with the subformulas reordered, used as a TLC
   init-state check to avoid generating unreachable states. *)
IndInv_Unforg_NoBcast_TLC ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc: pc[i] # "AC"
  /\ sent = {}
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

THEOREM NTFRel == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)
  BY NTF

ProcProp == Cardinality(Proc) = N /\ IsFiniteSet(Proc) /\ Cardinality(Proc) \in Nat
  BY FS_Interval, NTFRel

UMFS_CardinalityType ==
  \A X, Y, Z :
    /\ IsFiniteSet(X) /\ IsFiniteSet(Y) /\ IsFiniteSet(Z)
    /\ X \cup Y = Z /\ X = Z \ Y
    => Cardinality(X) = Cardinality(Z) - Cardinality(Y)
  <1>1 Cardinality(X) = Cardinality(Z) - Cardinality(Z \cap Y)
    BY FS_Difference
  <1>2 Z \cap Y = Y OBVIOUS
  <1>3 IsFiniteSet(Z \cap Y) BY FS_Intersection
  <1>4 Cardinality(Z \cap Y) = Cardinality(Y) BY <1>2
  <1> QED BY <1>1, <1>2, <1>3, <1>4

(* FCConstraints /\ TypeOK is an inductive invariant of SpecNoBcast. *)
FCConstraints_TypeOK_InitNoBcast ==
  InitNoBcast => FCConstraints /\ TypeOK
  <1>1 Corr \subseteq Proc OBVIOUS
  <1>2 Faulty \subseteq Proc OBVIOUS
  <1>3 IsFiniteSet(Corr) BY <1>1, ProcProp, FS_Subset
  <1>4 IsFiniteSet(Faulty) BY <1>2, ProcProp, FS_Subset
  <1>5 Corr \cup Faulty = Proc OBVIOUS
  <1>6 Faulty = Proc \ Corr OBVIOUS
  <1>7 Cardinality(Corr) >= N - T
    <2>1 Cardinality(Corr) \in Nat BY <1>3, FS_CardinalityType
    <2>2 Cardinality(Corr) >= N - F BY <2>1, NTFRel
    <2>3 N - F >= N - T BY NTFRel
    <2> QED BY <2>1, <2>2, <2>3, NTFRel
  <1>8 Cardinality(Faulty) <= T
    <2>1 Cardinality(Corr) \in Nat BY <1>3, FS_CardinalityType
    <2>2 Cardinality(Proc) - Cardinality(Corr) <= T BY <1>7, <2>1, ProcProp, NTFRel
    <2>3 Cardinality(Faulty) = Cardinality(Proc) - Cardinality(Corr) BY <1>3, <1>4, <1>5, <1>6, UMFS_CardinalityType, ProcProp
    <2> QED BY <2>2, <2>3
  <1>9 ByzMsgs \subseteq Proc \X M BY <1>2
  <1>10 IsFiniteSet(ByzMsgs)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2> QED BY <2>1, <1>4, FS_Product
  <1>11 Cardinality(ByzMsgs) = Cardinality(Faulty)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2>2 Cardinality(M) = 1 BY FS_Singleton
    <2>3 Cardinality(M) \in Nat BY <2>2
    <2>4 Cardinality(ByzMsgs) = Cardinality(Faulty) * Cardinality(M) BY <2>1, <1>4, FS_Product
    <2>5 Cardinality(ByzMsgs) \in Nat BY <1>10, FS_CardinalityType
    <2>6 Cardinality(Faulty) \in Nat BY <1>4, FS_CardinalityType
    <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6
  <1>12 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ] OBVIOUS
  <1>13 Corr \subseteq Proc OBVIOUS
  <1>14 Faulty \subseteq Proc OBVIOUS
  <1>15 sent \subseteq Proc \X M OBVIOUS
  <1>16 rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ] OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

FCConstraints_TypeOK_Init == Init => FCConstraints /\ TypeOK
  <1>1 Corr \subseteq Proc OBVIOUS
  <1>2 Faulty \subseteq Proc OBVIOUS
  <1>3 IsFiniteSet(Corr) BY <1>1, ProcProp, FS_Subset
  <1>4 IsFiniteSet(Faulty) BY <1>2, ProcProp, FS_Subset
  <1>5 Corr \cup Faulty = Proc OBVIOUS
  <1>6 Faulty = Proc \ Corr OBVIOUS
  <1>7 Cardinality(Corr) >= N - T
    <2>1 Cardinality(Corr) \in Nat BY <1>3, FS_CardinalityType
    <2>2 Cardinality(Corr) >= N - F BY <2>1, NTFRel
    <2>3 N - F >= N - T BY NTFRel
    <2> QED BY <2>1, <2>2, <2>3, NTFRel
  <1>8 Cardinality(Faulty) <= T
    <2>1 Cardinality(Corr) \in Nat BY <1>3, FS_CardinalityType
    <2>2 Cardinality(Proc) - Cardinality(Corr) <= T BY <1>7, <2>1, ProcProp, NTFRel
    <2> QED BY <1>3, <1>4, <1>5, <1>6, <2>2, UMFS_CardinalityType, ProcProp
  <1>9 ByzMsgs \subseteq Proc \X M BY <1>2
  <1>10 IsFiniteSet(ByzMsgs)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2> QED BY <2>1, <1>4, FS_Product
  <1>11 Cardinality(ByzMsgs) = Cardinality(Faulty)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2>2 Cardinality(M) = 1 BY FS_Singleton
    <2>3 Cardinality(M) \in Nat BY <2>2
    <2>4 Cardinality(ByzMsgs) = Cardinality(Faulty) * Cardinality(M) BY <2>1, <1>4, FS_Product
    <2>5 Cardinality(ByzMsgs) \in Nat BY <1>10, FS_CardinalityType
    <2>6 Cardinality(Faulty) \in Nat BY <1>4, FS_CardinalityType
    <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6
  <1>12 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ] OBVIOUS
  <1>13 Corr \subseteq Proc OBVIOUS
  <1>14 Faulty \subseteq Proc OBVIOUS
  <1>15 sent \subseteq Proc \X M OBVIOUS
  <1>16 rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ] OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
  BY DEF IndInv_Unforg_NoBcast

(* The reordered init-state check, used with depth-first search in TLC. *)
FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==
  IndInv_Unforg_NoBcast_TLC => FCConstraints
  <1>1 Corr \subseteq Proc OBVIOUS
  <1>2 Faulty \subseteq Proc OBVIOUS
  <1>3 IsFiniteSet(Corr) BY <1>1, ProcProp, FS_Subset
  <1>4 IsFiniteSet(Faulty) BY <1>2, ProcProp, FS_Subset
  <1>5 Corr \cup Faulty = Proc OBVIOUS
  <1>6 Faulty = Proc \ Corr OBVIOUS
  <1>7 Cardinality(Corr) >= N - T OBVIOUS
  <1>8 Cardinality(Faulty) <= T
    <2>1 Cardinality(Corr) \in Nat BY <1>3, FS_CardinalityType
    <2>2 Cardinality(Proc) - Cardinality(Corr) <= T BY <1>7, <2>1, ProcProp, NTFRel
    <2>3 QED BY <1>3, <1>4, <1>5, <1>6, <2>2, UMFS_CardinalityType, ProcProp
  <1>9 ByzMsgs \subseteq Proc \X M BY <1>2
  <1>10 IsFiniteSet(ByzMsgs)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2> QED BY <2>1, <1>4, FS_Product
  <1>11 Cardinality(ByzMsgs) = Cardinality(Faulty)
    <2>1 IsFiniteSet(M) BY FS_Singleton
    <2>2 Cardinality(M) = 1 BY FS_Singleton
    <2>3 Cardinality(M) \in Nat BY <2>2
    <2>4 Cardinality(ByzMsgs) = Cardinality(Faulty) * Cardinality(M) BY <2>1, <1>4, FS_Product
    <2>5 Cardinality(ByzMsgs) \in Nat BY <1>10, FS_CardinalityType
    <2>6 Cardinality(Faulty) \in Nat BY <1>4, FS_CardinalityType
    <2> QED BY <2>2, <2>3, <2>4, <2>5, <2>6
  <1>12 pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ] OBVIOUS
  <1>13 Corr \subseteq Proc OBVIOUS
  <1>14 Faulty \subseteq Proc OBVIOUS
  <1>15 sent \subseteq Proc \X M OBVIOUS
  <1>16 rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ] OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8, <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

FCConstraints_TypeOK_Next ==
  FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
  <1>1 FCConstraints' =
        /\ Corr' \subseteq Proc'
        /\ Faulty' \subseteq Proc'
        /\ IsFiniteSet(Corr')
        /\ IsFiniteSet(Faulty')
        /\ Corr' \cup Faulty' = Proc'
        /\ Faulty' = Proc' \ Corr'
        /\ Cardinality(Corr') >= N - T
        /\ Cardinality(Faulty') <= T
        /\ ByzMsgs' \subseteq Proc' \X M'
        /\ IsFiniteSet(ByzMsgs')
        /\ Cardinality(ByzMsgs') = Cardinality(Faulty')
    BY DEF FCConstraints
  <1>2 TypeOK' =
        /\ sent' \subseteq Proc' \X M'
        /\ pc' \in [ Proc' -> {"V0", "V1", "SE", "AC"} ]
        /\ Corr' \subseteq Proc'
        /\ Faulty' \subseteq Proc'
        /\ rcvd' \in [ Proc' -> SUBSET (sent' \cup ByzMsgs') ]
    BY DEF TypeOK
  <1>3 Proc' = Proc BY DEF Proc
  <1>4 M' = M OBVIOUS
  <1>5 CASE UNCHANGED vars
    <2>1 Corr' = Corr BY <1>5 DEF vars
    <2>2 Faulty' = Faulty BY <1>5 DEF vars
    <2>3 ByzMsgs' = ByzMsgs BY <2>2 DEF ByzMsgs
    <2>4 pc' \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
      BY <1>5 DEFS vars, TypeOK
    <2>5 sent \subseteq sent' BY <1>5 DEF vars
    <2>6 Faulty' = Faulty BY <1>5 DEF vars
    <2>7 ByzMsgs \subseteq ByzMsgs' BY <1>5, <2>2 DEF ByzMsgs
    <2>8 sent' \subseteq Proc' \X M' BY <1>5 DEFS vars, TypeOK, Proc, M
    <2>9 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
      <3>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <2>5, <2>7
      <3> QED BY <1>5, <3>1 DEFS vars, TypeOK, Receive
    <2>10 Corr' = Corr BY <1>5, <2>1, <2>3, <2>4, <2>8, <2>9 DEFS vars, FCConstraints, TypeOK
    <2> QED BY <1>5, <2>1, <2>3, <2>4, <2>8, <2>9
  <1>6 CASE Next
    <2>1 (\E i \in Corr: Step(i)) \/ UNCHANGED vars => FCConstraints' /\ TypeOK'
      <3>1 (\E i \in Corr: Step(i)) /\ FCConstraints /\ TypeOK => FCConstraints' /\ TypeOK'
        BY <1>6, <2>1
      <3>2 UNCHANGED vars /\ FCConstraints /\ TypeOK => FCConstraints' /\ TypeOK'
        BY <1>6, <2>1
      <3> QED BY <3>1, <3>2
    <2> QED BY <1>6

FCConstraints_TypeOK_SpecNoBcast == SpecNoBcast => [](FCConstraints /\ TypeOK)
  <1>1 InitNoBcast => FCConstraints /\ TypeOK BY FCConstraints_TypeOK_InitNoBcast
  <1>2 FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK' BY FCConstraints_TypeOK_Next
  <1> QED BY <1>1, <1>2, PTL DEF SpecNoBcast

(* Step 1: Init => IndInv *)
Unforg_Step1 == InitNoBcast => IndInv_Unforg_NoBcast
  <1>1 InitNoBcast => FCConstraints /\ TypeOK BY FCConstraints_TypeOK_InitNoBcast
  <1>2 InitNoBcast => sent = {} OBVIOUS
  <1>3 InitNoBcast => pc = [ i \in Proc |-> "V0" ] OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3

(* Step 2: IndInv /\ Next => IndInv' (together with a stuttering case) *)
Unforg_Step2 == IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1>1 IndInv_Unforg_NoBcast' =
        /\ TypeOK' /\ FCConstraints' /\ sent' = {} /\ pc' = [ i \in Proc |-> "V0" ]
    BY DEF IndInv_Unforg_NoBcast
  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
    <2>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => FCConstraints' /\ TypeOK'
      BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
    <2>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => (sent' = {} /\ pc' = [ j \in Proc |-> "V0" ])
      BY DEF IndInv_Unforg_NoBcast, vars
    <2> QED BY <2>1, <2>2
  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
    <2>1 CASE UNCHANGED vars
      <3>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast' BY <2>1
      <3> QED BY <1>2
    <2>2 CASE (\E i \in Corr: Step(i))
      <3>1 (\E i \in Corr: Step(i)) /\ IndInv_Unforg_NoBcast => IndInv_Unforg_NoBcast'
        BY <2>2
      <3>1 FCConstraints' /\ TypeOK' BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
      <3>2 sent' = {} /\ pc' = [ j \in Proc |-> "V0" ]
        <4>1 Step(i) <=>
                \/ ReceiveFromAnySender(i) /\ UponV1(i)
                \/ ReceiveFromAnySender(i) /\ UponNonFaulty(i)
                \/ ReceiveFromAnySender(i) /\ UponAcceptNotSentBefore(i)
                \/ ReceiveFromAnySender(i) /\ UponAcceptSentBefore(i)
                \/ ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
          BY DEF Step
        <4>2 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i)
               => Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
          <5>1 sent = {} OBVIOUS
          <5>2 sent \cup ByzMsgs = ByzMsgs OBVIOUS
          <5>3 rcvd[i] \subseteq sent \cup ByzMsgs BY TypeOK
          <5>4 rcvd[i] \subseteq ByzMsgs BY <5>3, <5>2
          <5>5 rcvd'[i] \subseteq ByzMsgs
            <6>1 Corr \subseteq Proc BY TypeOK
            <6>2 i \in Proc BY <6>1
            <6>3 ReceiveFromAnySender(i) <=> Receive(i, TRUE) BY DEF ReceiveFromAnySender
            <6>4 (IF TRUE THEN ByzMsgs ELSE {}) = ByzMsgs OBVIOUS
            <6>5 Receive(i, TRUE) <=>
                    (\E newMessages \in SUBSET ( sent \cup ByzMsgs ) :
                        rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY <6>4 DEF Receive
            <6>6 Receive(i, TRUE) <=>
                    (\E newMessages \in SUBSET ByzMsgs :
                        rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
              BY <5>1, <6>5
            <6>7 Receive(i, TRUE) BY <6>3
            <6>8 \E newMessages \in SUBSET ByzMsgs : rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ]
              BY <6>6, <6>7
            <6>9 rcvd'[i] \subseteq rcvd[i] \cup ByzMsgs
              <7>1 PICK newMessages \in SUBSET ByzMsgs :
                      rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ]
                BY <6>8
              <7>2 rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ] BY <7>1
              <7>3 rcvd'[i] = rcvd[i] \cup newMessages BY <6>2, <7>2
              <7>4 QED BY <5>4, <7>3
            <6>10 QED BY <5>4, <6>9, FCConstraints
          <5>6 Cardinality(Faulty) <= T BY FCConstraints
          <5>7 Cardinality(ByzMsgs) = Cardinality(Faulty) BY FCConstraints
          <5>8 Cardinality(ByzMsgs) <= T BY <5>6, <5>7
          <5>9 Cardinality(rcvd'[i]) <= Cardinality(ByzMsgs)
            <6>1 rcvd'[i] \in SUBSET ByzMsgs BY <5>5
            <6> QED BY <6>1, FS_Subset DEF FCConstraints
          <5>10 Cardinality(ByzMsgs) \in Nat BY FS_CardinalityType DEF FCConstraints
          <5>13 IsFiniteSet(rcvd'[i])
            <6>1 rcvd'[i] \in SUBSET ByzMsgs BY <5>5
            <6> QED BY <6>1, FS_Subset DEF FCConstraints
          <5>14 Cardinality(rcvd'[i]) \in Nat BY <5>13, FS_CardinalityType
          <5> QED BY <5>8, <5>10, <5>14, NTFRel
        <4>3 CASE ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
          BY <4>3 DEF IndInv_Unforg_NoBcast
        <4>4 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponV1(i)
          <5>1 ~UponV1(i) =
                  \/ ~(pc[i] = "V1") \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                  \/ ~(sent' = sent \cup { <<i, "ECHO">> }) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponV1
          <5>2 pc[i] = "V0"
            <6>1 i \in Corr OBVIOUS
            <6>2 i \in Proc BY IndInv_Unforg_NoBcast, FCConstraints
            <6> QED BY <6>2
          <5> QED BY <5>1, <5>2
        <4>5 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponNonFaulty(i)
          <5>1 ~UponNonFaulty(i) =
                  \/ ~(pc[i] \in { "V0", "V1" }) \/ ~(Cardinality(rcvd'[i]) >= N - 2 * T)
                  \/ ~(Cardinality(rcvd'[i]) < N - T) \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                  \/ ~(sent' = sent \cup { <<i, "ECHO">> }) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponNonFaulty
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponNonFaulty(i)
            <6>1 T < N - 2 * T BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2 * T BY <4>2, <6>1, <6>2, NTFRel
            <6> QED BY <5>1, NTFRel, <6>2, <6>3
          <5> QED BY <4>2, <5>2
        <4>6 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptNotSentBefore(i)
          <5>1 ~UponAcceptNotSentBefore(i) =
                  \/ ~(pc[i] \in { "V0", "V1" }) \/ ~(Cardinality(rcvd'[i]) >= N - T)
                  \/ ~(pc' = [pc EXCEPT ![i] = "AC"])
                  \/ ~(sent' = sent \cup { <<i, "ECHO">> }) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponAcceptNotSentBefore
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptNotSentBefore(i)
            <6>1 T < N - 2 * T BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2 * T BY <4>2, <6>1, <6>2, NTFRel
            <6>4 Cardinality(rcvd'[i]) < N - T BY <4>2, <6>3, NTFRel
            <6> QED BY <5>1, NTFRel, <6>2, <6>4
          <5> QED BY <4>2, <5>2
        <4>7 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptSentBefore(i)
          <5>1 ~UponAcceptSentBefore(i) =
                  \/ ~(pc[i] = "SE") \/ ~(Cardinality(rcvd'[i]) >= N - T)
                  \/ ~(pc' = [pc EXCEPT ![i] = "AC"])
                  \/ ~(sent' = sent) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponAcceptSentBefore
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptSentBefore(i)
            <6>1 T < N - 2 * T BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2 * T BY <4>2, <6>1, <6>2, NTFRel
            <6>4 Cardinality(rcvd'[i]) < N - T BY <4>2, <6>3, NTFRel
            <6> QED BY <5>1, NTFRel, <6>2, <6>4
          <5> QED BY <4>2, <5>2
        <4> QED BY <4>1, <4>3, <4>4, <4>5, <4>6, <4>7
      <3> QED BY <3>1, <3>2 DEF IndInv_Unforg_NoBcast
    <2>2 CASE UNCHANGED vars
      <3>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
        BY <2>2
      <3> QED BY <1>2
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3

(* Step 3, a safety property. *)
Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
  <1>1 pc = [i \in Proc |-> "V0"] => \A i \in Proc : pc[i] # "AC" OBVIOUS
  <1>2 (TypeOK /\ pc = [i \in Proc |-> "V0"]) => \A i \in Proc : pc[i] # "AC" BY <1>1
  <1>3 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0"]) => \A i \in Proc : pc[i] # "AC" BY <1>2
  <1>4 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0"] /\ sent = {}) => \A i \in Proc : pc[i] # "AC" BY <1>3
  <1>5 IndInv_Unforg_NoBcast => \A i \in Proc : pc[i] # "AC" BY <1>4 DEF IndInv_Unforg_NoBcast
  <1>6 IndInv_Unforg_NoBcast => \A i \in Proc : i \in Corr => pc[i] # "AC" BY <1>5
  <1> QED BY <1>6 DEF Unforg

(* Step 4: Spec => []Safety, a semantic safety theorem (not a real progress check). *)
Unforg_Step4 == SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast BY Unforg_Step1
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast' BY Unforg_Step2
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast BY <1>1, <1>2, PTL DEF SpecNoBcast
  <1>4 IndInv_Unforg_NoBcast => Unforg BY Unforg_Step3
  <1> QED BY <1>3, <1>4, PTL

=============================================================================