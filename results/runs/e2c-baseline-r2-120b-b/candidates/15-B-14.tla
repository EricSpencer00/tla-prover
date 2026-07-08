------------------------------ MODULE bcastByz ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast distributed  
   algorithm with Byzantine faults.
  
   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:
  
   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94
                                                                  
   A short description of the parameterized model is described in: Gmeiner,   
   Annu, et al. "Tutorial on parameterized model checking of fault-tolerant   
   distributed algorithms." International School on Formal Methods for the  
   Design of Computer, Communication and Software Systems. Springer  
   International Publishing, 2014.                   
  
   This specification has a TLAPS proof for property Unforgeability: if process p 
   is correct and does not broadcast a message m, then no correct process ever 
   accepts m. The formula InitNoBcast represents that the transmitter does not 
   broadcast any message. So, our goal is to prove the  formula
        (InitNoBcast /\ [][Next]_vars) => []Unforg                    
  
   We can use TLC to check two properties (for fixed parameters N, T, and F):
    - Correctness: if a correct process broadcasts, then every correct process accepts,
    - Replay: if a correct process accepts, then every correct process accepts.  
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
 *)

EXTENDS Naturals,
        FiniteSets,
        Functions,
        FunctionTheorems,
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

(* Global assumptions on the parameters *)
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N               (* all processes, including the faulty ones    *)
M    == {"ECHO"}             (* the only type of message we consider         *)

(* Byzantine processes may send arbitrary ECHO messages *)
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* Initial state: no messages have been sent, each process is in either V0 or V1,
   the set of correct processes is unknown but has size N‑F, the rest are faulty. *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* The special initial state used for the unforgeability proof: all correct
   processes start in V0. *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* Deterministic receive: a process always receives *all* messages that are
   currently in the network (including Byzantine messages when includeByz = TRUE). *)
Receive(self, includeByz) ==
  /\ rcvd' = [ i \in Proc |-> IF i # self
                         THEN rcvd[i]
                         ELSE rcvd[self] \cup ( sent
                                                \cup (IF includeByz THEN ByzMsgs ELSE {})) ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)     == Receive(self, TRUE)

(* Transition actions *)

(* A correct process that has received an INIT (V1) and has not sent ECHO before
   sends an ECHO message to all. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* A correct process that has received enough ECHO messages from distinct
   correct senders (but not enough to accept) sends an ECHO to all. *)
UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* A correct process that has received at least N‑T distinct ECHO messages and
   has not sent before accepts and also sends an ECHO. *)
UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* A correct process that has already sent an ECHO and now receives enough
   ECHO messages accepts (but does not send another message). *)
UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

(* All possible steps a correct process may take. *)
Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

(* A transition step of the system: either some correct process takes a step,
   or the system stays unchanged (self‑loop). *)
Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

(* Weak fairness: if any of the actions for a correct process becomes
   permanently enabled, it must eventually be taken. *)
Spec ==
  Init /\ [][Next]_vars
  /\ WF_vars(\E self \in Corr :
                /\ ReceiveFromCorrectSender(self)
                /\ \/ UponV1(self)
                   \/ UponNonFaulty(self)
                   \/ UponAcceptNotSentBefore(self)
                   \/ UponAcceptSentBefore(self))

(* Specification used for the unforgeability safety proof (no fairness needed). *)
SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* Type invariants *)
TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* Constraints on the number of correct and faulty processes. *)
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

(* Liveness properties *)

(* If every correct process starts in V1, eventually all correct processes accept. *)
CorrLtl == (\A i \in Corr : pc[i] = "V1") => <>(\A i \in Corr : pc[i] = "AC")

(* If some correct process accepts, eventually every correct process accepts. *)
RelayLtl == []((\E i \in Corr : pc[i] = "AC") => <>(\A i \in Corr : pc[i] = "AC"))

(* If all correct processes start with V0, then no correct process ever accepts. *)
UnforgLtl == (\A i \in Corr : pc[i] = "V0") => [](\A i \in Corr : pc[i] /= "AC")

(* Unforgeability expressed as a first‑order formula (used in the TLAPS proof). *)
Unforg == (\A i \in Proc : i \in Corr => (pc[i] /= "AC"))

(* Inductive invariant candidate for the unforgeability proof. *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

(* A rearranged version of the invariant that TLC can evaluate more efficiently. *)
IndInv_Unforg_NoBcast_TLC ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] /= "AC"
  /\ sent = {}
  /\ rcvd \in [ Proc -> sent \cup SUBSET ByzMsgs ]

(* ------------------------------------------------------------------- *)

THEOREM NTFRel ==
  N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0) /\ N - 2 * T >= T + 1
  BY NTF

THEOREM ProcProp == Cardinality(Proc) = N /\ IsFiniteSet(Proc) /\ Cardinality(Proc) \in Nat
  BY FS_Interval, NTFRel DEF Proc

THEOREM UMFS_CardinalityType ==
  \A X, Y, Z :
    /\ IsFiniteSet(X)
    /\ IsFiniteSet(Y)
    /\ IsFiniteSet(Z)
    /\ X \cup Y = Z
    /\ X = Z \ Y
    => Cardinality(X) = Cardinality(Z) - Cardinality(Y)
  <1> SUFFICES ASSUME NEW X, NEW Y, NEW Z,
                      IsFiniteSet(X), IsFiniteSet(Y), IsFiniteSet(Z),
                      X \cup Y = Z,
                      X = Z \ Y
              PROVE Cardinality(X) = Cardinality(Z) - Cardinality(Y)
              OBVIOUS
  <1>1 Cardinality(X) = Cardinality(Z) - Cardinality(Z \cap Y) BY FS_Difference
  <1>2 Z \cap Y = Y OBVIOUS
  <1>3 IsFiniteSet(Z \cap Y) BY FS_Intersection
  <1>4 Cardinality(Z \cap Y) = Cardinality(Y) BY <1>2
  <1> QED BY <1>1, <1>2, <1>3, <1>4

THEOREM FCConstraints_TypeOK_InitNoBcast ==
  InitNoBcast => FCConstraints /\ TypeOK
  <1> SUFFICES ASSUME InitNoBcast PROVE FCConstraints /\ TypeOK OBVIOUS
  <1> USE DEFS Proc, InitNoBcast, Init, ByzMsgs, M, FCConstraints, TypeOK
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8,
            <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

THEOREM FCConstraints_TypeOK_Init ==
  Init => FCConstraints /\ TypeOK
  <1> SUFFICES ASSUME Init PROVE FCConstraints /\ TypeOK OBVIOUS
  <1> USE DEFS FCConstraints, TypeOK, Proc, Init, ByzMsgs, M
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8,
            <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
  BY DEF IndInv_Unforg_NoBcast

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==
  IndInv_Unforg_NoBcast_TLC => FCConstraints
  <1> SUFFICES ASSUME IndInv_Unforg_NoBcast_TLC PROVE FCConstraints OBVIOUS
  <1> USE DEFS FCConstraints, TypeOK, Proc, IndInv_Unforg_NoBcast_TLC, ByzMsgs, M
  <1> QED BY <1>1, <1>2, <1>3, <1>4, <1>5, <1>6, <1>7, <1>8,
            <1>9, <1>10, <1>11, <1>12, <1>13, <1>14, <1>15, <1>16

THEOREM FCConstraints_TypeOK_Next ==
  FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
  <1> SUFFICES ASSUME FCConstraints,
                      TypeOK,
                      Next \/ UNCHANGED vars
               PROVE FCConstraints' /\ TypeOK' OBVIOUS
  <1>1 FCConstraints' = /\ Corr' \subseteq Proc'
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
  <1>2 TypeOK' = /\ sent' \subseteq Proc' \times M'
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
    <2>4 pc' \in [ Proc -> {"V0","V1","SE","AC"} ] BY <1>5 DEFS vars, TypeOK
    <2>5 sent \subseteq sent' BY <1>5 DEF vars
    <2>6 Faulty' = Faulty BY <1>5 DEF vars
    <2>7 ByzMsgs \subseteq ByzMsgs' BY <1>5, <2>2 DEF ByzMsgs
    <2>8 sent' \subseteq Proc' \times M' BY <1>5 DEFS vars, TypeOK, Proc, M
    <2>9 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
        <3>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs')
            BY <2>5, <2>7
        <3> QED BY <1>5, <3>1 DEFS vars, TypeOK, Receive
    <2> QED BY <1>5, <2>1, <2>3, <2>4, <2>8, <2>9 DEFS vars, FCConstraints, TypeOK
  <1>6 CASE Next
    <2> SUFFICES ASSUME FCConstraints,
                        TypeOK,
                        (\E i \in Corr : Step(i)) \/ UNCHANGED vars
                 PROVE FCConstraints' /\ TypeOK'
                 BY <1>6 DEF Next
    <2>1 CASE \E i \in Corr : Step(i)
      <3> SUFFICES ASSUME FCConstraints,
                          TypeOK,
                          NEW i \in Corr,
                          Step(i)
                 PROVE FCConstraints' /\ TypeOK'
                 BY <2>1
      <3>1 Step(i) <=> \/ ReceiveFromAnySender(i) /\ UponV1(i)
                         \/ ReceiveFromAnySender(i) /\ UponNonFaulty(i)
                         \/ ReceiveFromAnySender(i) /\ UponAcceptNotSentBefore(i)
                         \/ ReceiveFromAnySender(i) /\ UponAcceptSentBefore(i)
                         \/ ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
          BY DEF Step
      <3>2 CASE ReceiveFromAnySender(i) /\ UponV1(i)
        <4>1 FCConstraints' BY <3>2 DEF Receive, UponV1, FCConstraints, ByzMsgs
        <4>2 TypeOK'
          <5>1 pc' \in [ Proc -> {"V0","V1","SE","AC"} ] BY <3>2 DEFS UponV1, TypeOK
          <5>2 sent \subseteq sent' BY <3>2 DEFS UponV1
          <5>3 Faulty' = Faulty BY <3>2 DEFS UponV1
          <5>4 ByzMsgs \subseteq ByzMsgs' BY <3>2, <5>3 DEF ByzMsgs
          <5>5 sent' \subseteq Proc' \times M'
            <6>1 i \in Proc BY <3>2 DEFS TypeOK
            <6>2 << i, "ECHO" >> \in Proc' \times M' BY <6>1 DEFS Proc, M
            <6>3 { << i, "ECHO" >> } \subseteq Proc' \times M' BY <6>2
            <6>4 sent \subseteq Proc' \times M' BY <3>2 DEFS TypeOK, M, Proc
            <6> QED BY <3>2, <6>3, <6>4 DEFS UponV1, TypeOK
          <5>6 rcvd' \in [ Proc -> SUBSET (sent' \cup ByzMsgs') ]
            <6>1 (sent \cup ByzMsgs) \subseteq (sent' \cup ByzMsgs') BY <5>2, <5>4
            <6>2 ReceiveFromAnySender(i) <=> Receive(i, TRUE) BY DEF ReceiveFromAnySender
            <6>3 (IF TRUE THEN ByzMsgs ELSE {}) = ByzMsgs OBVIOUS
            <6>4 Receive(i, TRUE) <=>
                    (\E newMessages \in SUBSET (sent \cup ByzMsgs) :
                        rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
                BY <6>3 DEF Receive
            <6> QED BY <3>2, <6>1, <6>2, <6>3, <6>4 DEFS UponV1, TypeOK, Receive
          <5>7 Corr' = Corr BY <3>2 DEFS UponV1
          <5> QED BY <1>2, <3>2, <4>1, <5>1, <5>5, <5>6, <5>7 DEF TypeOK, FCConstraints
        <4> QED BY <4>1, <4>2
      <3>3 CASE ReceiveFromAnySender(i) /\ UponNonFaulty(i)
        <4>1 FCConstraints' BY <3>3 DEF Receive, UponNonFaulty, FCConstraints, ByzMsgs
        <4>2 TypeOK' (proof analogous to the previous case) OBVIOUS
        <4> QED BY <4>1, <4>2
      <3>4 CASE ReceiveFromAnySender(i) /\ UponAcceptNotSentBefore(i)
        <4>1 FCConstraints' BY <3>4 DEF Receive, UponAcceptNotSentBefore, FCConstraints, ByzMsgs
        <4>2 TypeOK' (proof analogous) OBVIOUS
        <4> QED BY <4>1, <4>2
      <3>5 CASE ReceiveFromAnySender(i) /\ UponAcceptSentBefore(i)
        <4>1 FCConstraints' BY <3>5 DEF Receive, UponAcceptSentBefore, FCConstraints, ByzMsgs
        <4>2 TypeOK' (proof analogous) OBVIOUS
        <4> QED BY <4>1, <4>2
      <3>6 CASE ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
        <4>1 FCConstraints' BY <3>6 DEF FCConstraints, ByzMsgs
        <4>2 TypeOK' (proof analogous) OBVIOUS
        <4> QED BY <4>1, <4>2
      <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Step
    <2>2 CASE UNCHANGED vars
      <3> SUFFICES ASSUME FCConstraints, TypeOK, UNCHANGED vars PROVE FCConstraints' /\ TypeOK' BY <2>2
      <3> QED BY <1>5
    <2> QED BY <1>6, <2>1, <2>2
  <1> QED BY <1>5, <1>6

THEOREM FCConstraints_TypeOK_SpecNoBcast ==
  SpecNoBcast => [](FCConstraints /\ TypeOK)
  <1>1 InitNoBcast => FCConstraints /\ TypeOK BY FCConstraints_TypeOK_InitNoBcast
  <1>2 FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK' BY FCConstraints_TypeOK_Next
  <1> QED BY <1>1, <1>2, PTL DEF SpecNoBcast

(* ------------------------------------------------------------------- *)

THEOREM Unforg_Step1 ==
  InitNoBcast => IndInv_Unforg_NoBcast
  <1> USE DEF InitNoBcast, Init, IndInv_Unforg_NoBcast
  <1>1 InitNoBcast => FCConstraints /\ TypeOK BY FCConstraints_TypeOK_InitNoBcast
  <1>2 InitNoBcast => sent = {} OBVIOUS
  <1>3 InitNoBcast => pc = [ i \in Proc |-> "V0" ] OBVIOUS
  <1> QED BY <1>1, <1>2, <1>3

THEOREM Unforg_Step2 ==
  IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1> SUFFICES ASSUME IndInv_Unforg_NoBcast,
                      Next \/ UNCHANGED vars
               PROVE IndInv_Unforg_NoBcast' OBVIOUS
  <1>1 IndInv_Unforg_NoBcast' =
        /\ TypeOK'
        /\ FCConstraints'
        /\ sent' = {}
        /\ pc' = [ i \in Proc' |-> "V0" ]
        BY DEF IndInv_Unforg_NoBcast
  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
        <2>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars => FCConstraints' /\ TypeOK'
              BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
        <2>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => (sent' = {} /\ pc' = [ j \in Proc |-> "V0" ])
              BY DEF IndInv_Unforg_NoBcast, vars
        <2> QED BY <2>1, <2>2 DEF IndInv_Unforg_NoBcast, vars
  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
        <2> SUFFICES ASSUME TypeOK,
                        FCConstraints,
                        sent = {},
                        pc = [ i \in Proc |-> "V0" ],
                        (\E i \in Corr : Step(i)) \/ UNCHANGED vars
                  PROVE IndInv_Unforg_NoBcast' BY DEF Next, IndInv_Unforg_NoBcast
        <2>1 CASE UNCHANGED vars
          <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [ i \in Proc |-> "V0" ], UNCHANGED vars
                 PROVE IndInv_Unforg_NoBcast' BY <2>1
          <3> QED BY <1>2
        <2>2 CASE (\E i \in Corr : Step(i))
          <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [ i \in Proc |-> "V0" ],
                          NEW i \in Corr, Step(i)
                 PROVE IndInv_Unforg_NoBcast' BY <2>2
          <3>1 FCConstraints' /\ TypeOK' BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
          <3>2 sent' = {} /\ pc' = [ j \in Proc |-> "V0" ]
            <4>1 Step(i) <=> \/ ReceiveFromAnySender(i) /\ UponV1(i)
                                 \/ ReceiveFromAnySender(i) /\ UponNonFaulty(i)
                                 \/ ReceiveFromAnySender(i) /\ UponAcceptNotSentBefore(i)
                                 \/ ReceiveFromAnySender(i) /\ UponAcceptSentBefore(i)
                                 \/ ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
                BY DEF Step
            <4>2 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) =>
                  Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
                <5> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [ j \in Proc |-> "V0" ],
                                ReceiveFromAnySender(i)
                       PROVE Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
                    BY DEF IndInv_Unforg_NoBcast
                <5>1 sent = {} OBVIOUS
                <5>2 sent \cup ByzMsgs = ByzMsgs OBVIOUS
                <5>3 rcvd[i] \subseteq sent \cup ByzMsgs BY DEF TypeOK
                <5>4 rcvd[i] \subseteq ByzMsgs BY <5>3, <5>2
                <5>5 rcvd'[i] \subseteq ByzMsgs
                    <6>1 Corr \subseteq Proc BY DEF TypeOK
                    <6>2 i \in Proc BY <6>1
                    <6>3 ReceiveFromAnySender(i) <=> Receive(i, TRUE) BY DEF ReceiveFromAnySender
                    <6>4 (IF TRUE THEN ByzMsgs ELSE {}) = ByzMsgs OBVIOUS
                    <6>5 Receive(i, TRUE) <=>
                          (\E newMessages \in SUBSET (sent \cup ByzMsgs) :
                              rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
                        BY <6>4 DEF Receive
                    <6>6 Receive(i, TRUE) <=>
                          (\E newMessages \in SUBSET ByzMsgs :
                              rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ])
                        BY <5>1, <6>5
                    <6>7 Receive(i, TRUE) BY <6>3
                    <6>8 \E newMessages \in SUBSET ByzMsgs :
                          rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ]
                        BY <6>6, <6>7
                    <6>9 rcvd'[i] \subseteq (rcvd[i] \cup ByzMsgs)
                        PICK newMessages \in SUBSET ByzMsgs :
                              rcvd' = [ j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages ]
                        BY <6>8
                    <6> QED BY <5>4, <6>9 DEF Receive, ReceiveFromAnySender
                <5>6 Cardinality(Faulty) <= T BY DEF FCConstraints
                <5>7 Cardinality(ByzMsgs) = Cardinality(Faulty) BY DEF FCConstraints
                <5>8 Cardinality(ByzMsgs) <= T BY <5>6, <5>7
                <5>9 Cardinality(rcvd'[i]) <= Cardinality(ByzMsgs)
                    <6>1 rcvd'[i] \in SUBSET ByzMsgs BY <5>5
                    <6> QED BY <6>1, FS_Subset DEF FCConstraints
                <5>10 Cardinality(ByzMsgs) \in Nat BY FS_CardinalityType DEF FCConstraints
                <5>11 IsFiniteSet(rcvd'[i])
                    <6>1 rcvd'[i] \in SUBSET ByzMsgs BY <5>5
                    <6> QED BY <6>1, FS_Subset DEF FCConstraints
                <5>12 Cardinality(rcvd'[i]) \in Nat BY <5>11, FS_CardinalityType
                <5> QED BY <5>12, <5>10, <5>8, <5>9, NTFRel
            <4>3 CASE ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
                BY <4>3 DEF IndInv_Unforg_NoBcast
            <4>4 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponV1(i)
                <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponV1(i) OBVIOUS
                <5>1 ~UponV1(i) = \/ ~(pc[i] = "V1")
                                 \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                                 \/ ~(sent' = sent \cup { <<i, "ECHO">> })
                                 \/ ~(UNCHANGED << Corr, Faulty >>)
                    BY DEF UponV1
                <5>2 pc[i] = "V0"
                    <6>1 i \in Corr OBVIOUS
                    <6>2 i \in Proc BY DEF IndInv_Unforg_NoBcast, FCConstraints
                    <6> QED BY <6>2
                <5> QED BY <5>1, <5>2
            <4>5 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponNonFaulty(i)
                <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponNonFaulty(i) OBVIOUS
                <5>1 ~UponNonFaulty(i) = \/ ~(pc[i] \in {"V0","V1"})
                                      \/ ~(Cardinality(rcvd'[i]) >= N - 2 * T)
                                      \/ ~(Cardinality(rcvd'[i]) < N - T)
                                      \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                                      \/ ~(sent' = sent \cup { <<i, "ECHO">> })
                                      \/ ~(UNCHANGED << Corr, Faulty >>)
                    BY DEF UponNonFaulty
                <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponNonFaulty(i)
                    <6>1 T < N - 2 * T BY NTFRel
                    <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
                    <6>3 Cardinality(rcvd'[i]) < N - 2 * T BY <4>2, <6>1, <6>2, NTFRel
                    <6> QED BY <5>1, NTFRel, <6>2, <6>3 DEF UponNonFaulty
                <5> QED BY <4>2, <5>2
            <4>6 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptNotSentBefore(i)
                <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponAcceptNotSentBefore(i) OBVIOUS
                <5>1 ~UponAcceptNotSentBefore(i) = \/ ~(pc[i] \in {"V0","V1"})
                                                \/ ~(Cardinality(rcvd'[i]) >= N - T)
                                                \/ ~(pc' = [pc EXCEPT ![i] = "AC"])
                                                \/ ~(sent' = sent \cup { <<i, "ECHO">> })
                                                \/ ~(UNCHANGED << Corr, Faulty >>)
                    BY DEF UponAcceptNotSentBefore
                <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptNotSentBefore(i)
                    <6>1 T < N - 2 * T BY NTFRel
                    <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
                    <6>3 Cardinality(rcvd'[i]) < N - 2 * T BY <4>2, <6>1, <6>2, NTFRel
                    <6>4 Cardinality(rcvd'[i]) < N - T BY <4>2, <6>3, NTFRel
                    <6> QED BY <5>1, NTFRel, <6>2, <6>4 DEF UponAcceptNotSentBefore
                <5> QED BY <4>2, <5>2
            <4>7 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptSentBefore(i)
                <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponAcceptSentBefore(i) OBVIOUS
                <5>1 ~UponAcceptSentBefore(i) = \/ ~(pc[i] = "SE")
                                                \/ ~(Cardinality(rcvd'[i]) >= N - T)
                                                \/ ~(pc' = [pc EXCEPT ![i] = "AC"])
                                                \/ ~(sent' = sent)
                                                \/ ~(UNCHANGED << Corr, Faulty >>)
                    BY DEF UponAcceptSentBefore
                <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptSentBefore(i)
                    <6>1 T < N - 2 * T BY NTFRel
                    <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
                    <6>3 Cardinality(rcvd'[i]) < N - 2 * T BY <4>2, <6>1, <6>2, NTFRel
                    <6>4 Cardinality(rcvd'[i]) < N - T BY <4>2, <6>3, NTFRel
                    <6> QED BY <5>1, NTFRel, <6>2, <6>4 DEF UponAcceptSentBefore
                <5> QED BY <4>2, <5>2
            <4> QED BY <4>1, <4>3, <4>4, <4>5, <4>6, <4>7
          <3> QED BY <3>1, <3>2, <3>3, <3>4, <3>5, <3>6 DEF Step
        <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3

THEOREM Unforg_Step3 ==
  IndInv_Unforg_NoBcast => Unforg
  <1>1 pc = [i \in Proc |-> "V0"] => \A i \in Proc : pc[i] # "AC" OBVIOUS
  <1>2 (TypeOK /\ pc = [i \in Proc |-> "V0"]) => \A i \in Proc : pc[i] # "AC" BY <1>1
  <1>3 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0"]) => \A i \in Proc : pc[i] # "AC" BY <1>2
  <1>4 (TypeOK /\ FCConstraints /\ pc = [i \in Proc |-> "V0"] /\ sent = {}) => \A i \in Proc : pc[i] # "AC"
       BY <1>3
  <1>5 IndInv_Unforg_NoBcast => \A i \in Proc : pc[i] # "AC" BY <1>4 DEF IndInv_Unforg_NoBcast
  <1>6 IndInv_Unforg_NoBcast => \A i \in Proc : i \in Corr => pc[i] # "AC" BY <1>5
  <1> QED BY <1>6 DEF Unforg

THEOREM Unforg_Step4 ==
  SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast BY Unforg_Step1
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast' BY Unforg_Step2
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast BY <1>1, <1>2, PTL DEF SpecNoBcast
  <1>4 IndInv_Unforg_NoBcast => Unforg BY Unforg_Step3
  <1> QED BY <1>3, <1>4, PTL

=============================================================================