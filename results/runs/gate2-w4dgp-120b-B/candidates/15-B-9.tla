------------------------------ MODULE bcastByz ------------------------------
(* TLA+ encoding of a parameterized model of the broadcast distributed
   algorithm with Byzantine faults.

   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94

   A short description of the parameterized model is described in:
   Gmeiner, Annu, et al. "Tutorial on parameterized model checking of fault-
   tolerant distributed algorithms." International School on Formal Methods for the
   Design of Computer, Communication and Software Systems. Springer International
   Publishing, 2014.

   This specification has a TLAPS proof for property Unforgeability: if process p is
   correct and does not broadcast a message m, then no correct process ever accepts,
   m. The formula InitNoBcast represents that the transmitter does not broadcast any
   message, so we prove the  formula (InitNoBcast /\ [][Next]_vars) => []Unforg

   We can use TLC to check two properties (for fixed N, T, and F):
     - Correctness: if a correct process broadcasts, then every correct process accepts,
     - Replay: if a correct process accepts, then every correct process accepts.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

   This file is subject to the license bundled with this package, see LICENSE. *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* instead of modeling a broadcaster explicitly, two initial values V0 and V1 at correct
   processes are used to model whether a process has received the INIT message from the
   broadcaster: V1 if it has, V0 otherwise. The precondition of correctness is that all
   correct processes initially have V1, and the precondition of unforgeability is that all
   correct processes initially have V0. *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* the special case of Init in which every correct process has V0 *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* a correct process can receive all ECHO messages from correct processes and any from the
   Byzantine ones (includeByz = FALSE excludes the Byzantine messages) *)
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)       == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* a correct process that has not yet sent ECHO messages receives from at least N-2T distinct
   processes and sends ECHO to all *)
UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* a process that has not yet sent ECHO and receives from at least N-T distinct
   processes accepts and sends ECHO to all *)
UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* a process that has already sent ECHO accepts once it receives from at least N-T distinct
   processes *)
UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self) \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self) \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec     == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

FCConstraints ==
  /\ Corr \subseteq Proc /\ Faulty \subseteq Proc /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr /\ Cardinality(Corr) >= N - T /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* if a correct process broadcasts, then every correct process accepts *)
CorrLtl == (\A i \in Corr: pc[i] = "V1") => <>(\A i \in Corr: pc[i] = "AC")

(* if a correct process accepts, then every correct process accepts *)
RelayLtl == []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

(* if no correct process broadcasts then no correct process accepts *)
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] # "AC")

(* the special case of Unforgeability when InitNoBcast holds *)
Unforg == (\A i \in Proc: i \in Corr => pc[i] # "AC")

(* the inductive invariant used to prove safety: no messages are sent and every process
   is in V0 *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK /\ FCConstraints /\ sent = {} /\ pc = [ i \in Proc |-> "V0" ]

(* IndInv_Unforg_NoBcast is an inductive invariant of SpecNoBcast *)
Unforg_Step1 ==
  InitNoBcast => IndInv_Unforg_NoBcast
Unforg_Step2 ==
  IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
Unforg_Step4 == SpecNoBcast => []Unforg

THEOREM NTFRel == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0 /\ N - 2 * T >= T + 1
  BY NTF

THEOREM FCConstraints_TypeOK_InitNoBcast ==
  InitNoBcast => FCConstraints /\ TypeOK
  BY DEF InitNoBcast, Init, FCConstraints, TypeOK

THEOREM FCConstraints_TypeOK_Init ==
  Init => FCConstraints /\ TypeOK
  BY DEF Init, FCConstraints, TypeOK

THEOREM UMFS_CardinalityType ==
  \A X, Y, Z :
    /\ IsFiniteSet(X) /\ IsFiniteSet(Y) /\ IsFiniteSet(Z)
    /\ X \cup Y = Z /\ X = Z \ Y
    => Cardinality(X) = Cardinality(Z) - Cardinality(Y)
  <1>1 Cardinality(X) = Cardinality(Z) - Cardinality(Z \cap Y) BY FS_Difference
  <1>2 Z \cap Y = Y OBVIOUS
  <1>3 IsFiniteSet(Z \cap Y) BY FS_Intersection
  <1>4 Cardinality(Z \cap Y) = Cardinality(Y) BY <1>2
  <1> QED BY <1>1, <1>2, <1>3, <1>4

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast ==
  IndInv_Unforg_NoBcast => FCConstraints /\ TypeOK
  BY DEF IndInv_Unforg_NoBcast

THEOREM FCConstraints_TypeOK_IndInv_Unforg_NoBcast_TLC ==
  IndInv_Unforg_NoBcast => FCConstraints
  <1>1 IndInv_Unforg_NoBcast =>
        /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
        /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
        /\ sent \subseteq Proc \times M
        /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]
  <1>2 (\A i \in Proc: pc[i] # "AC") =>
        /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
        /\ Faulty = Proc \ Corr /\ Cardinality(Corr) >= N - T /\ Cardinality(Faulty) <= T
        /\ ByzMsgs \subseteq Proc \X M /\ IsFiniteSet(ByzMsgs)
        /\ Cardinality(ByzMsgs) = Cardinality(Faulty)
  <1> QED BY <1>1, <1>2, NTF

THEOREM FCConstraints_TypeOK_SpecNoBcast ==
  SpecNoBcast => [] (FCConstraints /\ TypeOK)
  <1>1 InitNoBcast => FCConstraints /\ TypeOK
    BY FCConstraints_TypeOK_InitNoBcast
  <1>2 FCConstraints /\ TypeOK /\ [Next]_vars => FCConstraints' /\ TypeOK'
    BY DEF FCConstraints, TypeOK, Next, vars
  <1> QED BY <1>1, <1>2, PTL DEF SpecNoBcast

THEOREM Unforg_Step2 ==
  IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1>1 IndInv_Unforg_NoBcast' =
        /\ TypeOK' /\ FCConstraints'
        /\ sent' = {} /\ pc' = [j \in Proc |-> "V0"]
    BY DEF IndInv_Unforg_NoBcast
  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
    <2>1 IndInv_Unforg_NoBcast /\ UNCHANGED vars =>
          FCConstraints' /\ TypeOK'
      BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
    <2>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars =>
          (sent' = {} /\ pc' = [j \in Proc |-> "V0"])
      BY DEF IndInv_Unforg_NoBcast, vars
    <2> QED BY <2>1, <2>2
  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
    <2>1 IndInv_Unforg_NoBcast /\ Next =>
          /\ FCConstraints' /\ TypeOK'
          /\ sent' = {} /\ pc' = [j \in Proc |-> "V0"]
      BY <1>1, <1>2
    <2> QED BY <2>1, <1>2
  <1> QED BY <1>2, <1>3

THEOREM Unforg_Step3 == IndInv_Unforg_NoBcast => Unforg
  <1>1 (\A i \in Proc: pc[i] # "AC") <=>
        /\ (\A i \in Proc: pc[i] \in {"V0", "V1"}) /\ sent = {}
        /\ (\A i \in Proc: ~UponV1(i))
        /\ (\A i \in Proc: ~UponNonFaulty(i))
        /\ (\A i \in Proc: ~UponAcceptNotSentBefore(i))
        /\ (\A i \in Proc: ~UponAcceptSentBefore(i))
    BY <1>1 DEF UponV1, UponNonFaulty, UponAcceptNotSentBefore, UponAcceptSentBefore
  <1> QED BY <1>1 DEF IndInv_Unforg_NoBcast

THEOREM Unforg_Step4 == SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast
    BY Unforg_Step1
  <1>2 IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
    BY Unforg_Step2
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast
    BY <1>1, <1>2, PTL DEF SpecNoBcast
  <1>4 IndInv_Unforg_NoBcast => Unforg
    BY Unforg_Step3
  <1> QED BY <1>3, <1>4, PTL

=============================================================================