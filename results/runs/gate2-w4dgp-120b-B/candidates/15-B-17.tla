------------------------------ MODULE bcastByz ------------------------------
(* TLA+ encoding of a parameterized model of the broadcast distributed
   algorithm with Byzantine faults.

   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94

   A short description of the parameterized model is described in:
   Gmeiner, Annu, et al. "Tutorial on parameterized model checking of fault-tolerant
   distributed algorithms." International School on Formal Methods for the
   Design of Computer, Communication and Software Systems. Springer
   International Publishing, 2014.

   This specification has a TLAPS proof for property Unforgeability: if process p
   is correct and does not broadcast a message m, then no correct process ever
   accepts m. The formula InitNoBcast represents that the transmitter does not
   broadcast any message. So, we prove (InitNoBcast /\ [][Next]_vars) => []Unforg.

   We can use TLC to check two properties (for fixed parameters N, T, and F):
    - Correctness: if a correct process broadcasts, then every correct process accepts,
    - Replay: if a correct process accepts, then every correct process accepts.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

   This file is subject to the license bundled with this package (see LICENSE). *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

(* A correct process can receive all ECHO messages sent by the other correct
   processes (a subset of sent) and all possible (arbitrary) ECHO messages from
   the Byzantine processes (a subset of ByzMsgs). If includeByz is FALSE, the
   Byzantine messages are not included. *)
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]
ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self) == Receive(self, TRUE)

(* The first if-then in Fig. 7: p received an INIT and did not send ECHO before,
   so it sends ECHO to all. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* The third if-then in Fig. 7: a correct p received ECHO from at least N-2T
   distinct processes and did not send ECHO before, so it sends ECHO to all. *)
UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* The 2nd and 3rd if-then in Fig. 7: p received ECHO from at least N-T distinct
   processes (and did not send ECHO before), so it accepts and sends ECHO. *)
UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* The 2nd if-then in Fig. 7: p sent ECHO and received from at least N-T, so it
   accepts. *)
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

Next == \/ \E self \in Corr: Step(self) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
            /\ WF_vars(\E self \in Corr: /\ ReceiveFromCorrectSender(self)
                                     /\ \/ UponV1(self) \/ UponNonFaulty(self)
                                        \/ UponAcceptNotSentBefore(self)
                                        \/ UponAcceptSentBefore(self))

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* InitNoBcast: the restricted case where no correct process received an INIT. *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* FCConstraints is an invariant: Corr and Faulty are disjoint subsets of Proc,
   all faulty processes are known, the number of correct processes is at least
   N-T, and the number of Byzantine messages is the number of faulty processes. *)
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

(* Undefinable unforgeability: no correct process accepts. *)
UnforgLtl == (\A i \in Corr: pc[i] = "V0") => [](\A i \in Corr: pc[i] # "AC")
Unforg == (\A i \in Proc: i \in Corr => (pc[i] # "AC"))

(* The inductive invariant for InitNoBcast. *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

THEOREM InitNoBcast => IndInv_Unforg_NoBcast
  BY DEF InitNoBcast, Init, IndInv_Unforg_NoBcast

THEOREM IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  <1> SUFFICES ASSUME IndInv_Unforg_NoBcast,
                      Next \/ UNCHANGED vars
               PROVE IndInv_Unforg_NoBcast'
        OBVIOUS
  <1>1 IndInv_Unforg_NoBcast' = /\
      TypeOK' /\ FCConstraints' /\ sent' = {} /\ pc' = [i \in Proc |-> "V0"]
    BY DEF IndInv_Unforg_NoBcast
  <1>2 IndInv_Unforg_NoBcast /\ UNCHANGED vars => IndInv_Unforg_NoBcast'
    BY DEF IndInv_Unforg_NoBcast, vars
  <1>3 IndInv_Unforg_NoBcast /\ Next => IndInv_Unforg_NoBcast'
    <2> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [i \in Proc |-> "V0"],
                      (\E i \in Corr: Step(i)) \/ UNCHANGED vars
                 PROVE IndInv_Unforg_NoBcast'
                 BY DEF Next, IndInv_Unforg_NoBcast
    <2>1 CASE UNCHANGED vars
      <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [i \in Proc |-> "V0"], UNCHANGED vars
                   PROVE IndInv_Unforg_NoBcast'
                   BY <2>1
      <3> QED BY <1>2
    <2>2 CASE (\E i \in Corr: Step(i))
      <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [i \in Proc |-> "V0"],
                      NEW i \in Corr, Step(i)
                 PROVE IndInv_Unforg_NoBcast'
                 BY <2>2
      <3>1 FCConstraints' /\ TypeOK'
        BY FCConstraints_TypeOK_Next DEF IndInv_Unforg_NoBcast
      <3>2 sent' = {} /\ pc' = [j \in Proc |-> "V0"]
        <4>1 Step(i) <=> \/ ReceiveFromAnySender(i) /\ UponV1(i)
                          \/ ReceiveFromAnySender(i) /\ UponNonFaulty(i)
                          \/ ReceiveFromAnySender(i) /\ UponAcceptNotSentBefore(i)
                          \/ ReceiveFromAnySender(i) /\ UponAcceptSentBefore(i)
                          \/ ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
          BY DEF Step
        <4>2 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) =>
              (Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat)
          <5> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [j \in Proc |-> "V0"],
                           ReceiveFromAnySender(i)
                     PROVE Cardinality(rcvd'[i]) <= T /\ Cardinality(rcvd'[i]) \in Nat
              BY DEF IndInv_Unforg_NoBcast
          <5>1 sent = {}
            OBVIOUS
          <5>2 rcvd[i] \subseteq ByzMsgs
            BY DEF TypeOK
          <5>3 rcvd'[i] \subseteq ByzMsgs
            <6>1 ReceiveFromAnySender(i) <=> Receive(i, TRUE)
              BY DEF ReceiveFromAnySender
            <6>2 (IF TRUE THEN ByzMsgs ELSE {}) = ByzMsgs BY OBVIOUS
            <6>3 Receive(i, TRUE) <=>
                  (\E newMessages \in SUBSET ByzMsgs : rcvd' = [j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages])
              BY <6>2 DEF Receive
            <6>4 Receive(i, TRUE)
              BY <6>1, <6>3
            <6>5 \E newMessages \in SUBSET ByzMsgs : rcvd' = [j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages]
              BY <6>3, <6>4
            <6>6 rcvd'[i] \subseteq (rcvd[i] \cup ByzMsgs)
              <7>1 PICK newMessages \in SUBSET ByzMsgs:
                        rcvd' = [j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages]
                BY <6>5
              <7>2 rcvd' = [j \in Proc |-> IF j # i THEN rcvd[j] ELSE rcvd[i] \cup newMessages]
                BY <7>1
              <7>3 rcvd'[i] = rcvd[i] \cup newMessages
                BY <6>2, <7>2
              <7> QED
                BY <5>2, <7>3
            <6> QED BY <5>1, <5>2, <6>1, <6>2, <6>3, <6>4
          <5>4 Cardinality(Faulty) <= T
            BY DEF FCConstraints
          <5>5 Cardinality(ByzMsgs) = Cardinality(Faulty)
            BY DEF FCConstraints
          <5>6 Cardinality(ByzMsgs) <= T
            BY <5>4, <5>5
          <5>7 Cardinality(rcvd'[i]) <= Cardinality(ByzMsgs)
            <6>1 rcvd'[i] \in SUBSET ByzMsgs
              BY <5>3
            <6> QED BY <6>1, FS_Subset, FCConstraints
          <5>8 Cardinality(ByzMsgs) \in Nat
            BY FS_CardinalityType, FCConstraints
          <5>9 IsFiniteSet(rcvd'[i])
            <6>1 rcvd'[i] \in SUBSET ByzMsgs
              BY <5>3
            <6> QED BY <6>1, FS_Subset, FCConstraints
          <5>10 Cardinality(rcvd'[i]) \in Nat
            BY <5>9, FS_CardinalityType
          <5> QED BY <5>7, <5>8, <5>6, NTFRel
        <4>3 CASE ReceiveFromAnySender(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
          BY DEF IndInv_Unforg_NoBcast
        <4>4 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponV1(i)
          <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponV1(i)
              OBVIOUS
          <5>1 ~UponV1(i) =
                  \/ ~(pc[i] = "V1") \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                    \/ ~(sent' = sent \cup {<<i, "ECHO">>}) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponV1
          <5>2 pc[i] = "V0" BY <5>1, IndInv_Unforg_NoBcast, FCConstraints
          <5> QED BY <5>1, <5>2
        <4>5 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponNonFaulty(i)
          <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponNonFaulty(i)
              OBVIOUS
          <5>1 ~UponNonFaulty(i) =
                  \/ ~(pc[i] \in {"V0", "V1"}) \/ ~(Cardinality(rcvd'[i]) >= N - 2*T)
                    \/ ~(Cardinality(rcvd'[i]) < N - T) \/ ~(pc' = [pc EXCEPT ![i] = "SE"])
                    \/ ~(sent' = sent \cup {<<i, "ECHO">>}) \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponNonFaulty
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponNonFaulty(i)
            <6>1 T < N - 2*T BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2*T BY <4>2, <6>1, <6>2, NTFRel
            <6> QED BY <5>1, NTFRel, <6>2, <6>3, IndInv_Unforg_NoBcast
          <5> QED BY <4>2, <5>2
        <4>6 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptNotSentBefore(i)
          <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponAcceptNotSentBefore(i)
              OBVIOUS
          <5>1 ~UponAcceptNotSentBefore(i) =
                  \/ ~(pc[i] \in {"V0", "V1"}) \/ ~(Cardinality(rcvd'[i]) >= N - T)
                    \/ ~(pc' = [pc EXCEPT ![i] = "AC"]) \/ ~(sent' = sent \cup {<<i, "ECHO">>})
                    \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponAcceptNotSentBefore
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptNotSentBefore(i)
            <6>1 T < N - 2*T BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2*T BY <4>2, <6>1, <6>2, NTFRel
            <6>4 Cardinality(rcvd'[i]) < N - T BY <4>2, <6>3, NTFRel
            <6> QED BY <5>1, NTFRel, <6>2, <6>4, IndInv_Unforg_NoBcast
          <5> QED BY <4>2, <5>2
        <4>7 IndInv_Unforg_NoBcast /\ ReceiveFromAnySender(i) => ~UponAcceptSentBefore(i)
          <5> SUFFICES ASSUME IndInv_Unforg_NoBcast, ReceiveFromAnySender(i) PROVE ~UponAcceptSentBefore(i)
              OBVIOUS
          <5>1 ~UponAcceptSentBefore(i) =
                  \/ ~(pc[i] = "SE") \/ ~(Cardinality(rcvd'[i]) >= N - T)
                    \/ ~(pc' = [pc EXCEPT ![i] = "AC"]) \/ ~(sent' = sent)
                    \/ ~(UNCHANGED << Corr, Faulty >>)
            BY DEF UponAcceptSentBefore
          <5>2 (Cardinality(rcvd'[i]) <= T) => ~UponAcceptSentBefore(i)
            <6>1 T < N - 2*T BY NTFRel
            <6>2 Cardinality(rcvd'[i]) \in Nat BY <4>2
            <6>3 Cardinality(rcvd'[i]) < N - 2*T BY <4>2, <6>1, <6>2, NTFRel
            <6>4 Cardinality(rcvd'[i]) < N - T BY <4>2, <6>3, NTFRel
            <6> QED BY <5>1, NTFRel, <6>2, <6>4, IndInv_Unforg_NoBcast
          <5> QED BY <4>2, <5>2
        <4> QED BY <4>1, <4>3, <4>4, <4>5, <4>6, <4>7
      <3> QED BY <3>1, <3>2, IndInv_Unforg_NoBcast
    <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3

THEOREM IndInv_Unforg_NoBcast => Unforg
  <1>1 pc = [i \in Proc |-> "V0"] => \A i \in Proc : pc[i] # "AC"
    OBVIOUS
  <1> QED BY <1>1, DEF IndInv_Unforg_NoBcast

THEOREM InitNoBcast => IndInv_Unforg_NoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg_NoBcast
    BY InitNoBcast => IndInv_Unforg_NoBcast
  <1>2 IndInv_Unforg_NoBcast /\ [][Next]_vars => IndInv_Unforg_NoBcast'
    BY IndInv_Unforg_NoBcast /\ [][Next]_vars => IndInv_Unforg_NoBcast'
  <1>3 SpecNoBcast => []IndInv_Unforg_NoBcast
    BY <1>1, <1>2, PTL DEF InitNoBcast, Spec
  <1>4 IndInv_Unforg_NoBcast => Unforg
    BY IndInv_Unforg_NoBcast => Unforg
  <1> QED BY <1>3, <1>4, PTL

=============================================================================