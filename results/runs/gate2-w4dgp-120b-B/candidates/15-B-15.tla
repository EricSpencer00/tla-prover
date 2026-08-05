------------------------------ MODULE bcastByz ------------------------------
(* TLA+ encoding of a parameterized model of the broadcast distributed algorithm
   with Byzantine faults.

   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94

   A short description of the parameterized model is described in:
   Gmeiner, Annu, et al. "Tutorial on parameterized model checking of fault-
   tolerant distributed algorithms." International School on Formal Methods for
   the Design of Computer, Communication and Software Systems.
   Springer International Publishing, 2014.

   This specification has a TLAPS proof for property Unforgeability: if a correct
   process p is correct and does not broadcast a message m, then no correct process
   ever accepts m. The formula InitNoBcast states that the transmitter does not
   broadcast any message. So, we can prove (InitNoBcast /\ [][Next]_vars) =>
   []Unforg.  AFC (InitNoBcast) and the strong fairness condition (WF_vars) are
   used to check the safety property.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

   This file has a TLAPS proof for Unforgeability and a liveness check with TLC.
 *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
          NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

VARIABLES Corr, Faulty, pc, rcvd, sent

vars == << Corr, Faulty, pc, rcvd, sent >>

Proc == 1 .. N

M == { "ECHO" }
ByzMsgs == Faulty \X M

Init ==
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]

(* InitNoBcast is the special case where all correct processes initially have value V0,
   i.e., the broadcast transmitter sent no INIT messages to any correct process. *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

TypeOK ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

FCConstraints ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

\* A correct process receives all ECHO messages from the other correct process
\* and any subset of ECHO messages from the Byzantine processes.
Receive(self, includeByz) ==
  \E newMessages \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup newMessages
                              ELSE rcvd[i] ]

ReceiveFromCorrect(self) == Receive(self, FALSE)
ReceiveFromAny(self)      == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { << self, "ECHO" >> }
  /\ UNCHANGED << Corr, Faulty >>

\* With only correct senders, a process executes the 3rd if-then only if it has
\* not already executed the 2nd if-then, since the message count is below N - T.
UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { << self, "ECHO" >> }
  /\ UNCHANGED << Corr, Faulty >>

\* The 2nd and 3rd if-then of Fig. 7 [1].
UponAcceptNotSent(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { << self, "ECHO" >> }
  /\ UNCHANGED << Corr, Faulty >>

\* The 2nd if-then only, after already sending an ECHO message.
UponAcceptSent(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ UNCHANGED << sent, Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAny(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSent(self)
     \/ UponAcceptSent(self)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

Spec ==
  Init /\ [][Next]_vars
       /\ WF_vars(\E self \in Corr : /\ ReceiveFromCorrect(self)
                              /\ \/ UponV1(self)
                                 \/ UponNonFaulty(self)
                                 \/ UponAcceptNotSent(self)
                                 \/ UponAcceptSent(self))

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* If a correct process broadcasts, every correct process eventually accepts. *)
Correctness == (\A i \in Corr : pc[i] = "V1") => <>(\A i \in Corr : pc[i] = "AC")

(* If a correct process accepts, every correct process accepts. *)
Relay == []((\E i \in Corr : pc[i] = "AC") => <>(\A i \in Corr : pc[i] = "AC"))

(* Safety: if no correct process broadcasts, no correct process accepts. *)
Unforgeability == (\A i \in Corr : pc[i] = "V0") => [](\A i \in Corr : pc[i] # "AC")

(* The special case of Unforgeability under InitNoBcast. *)
Unforg == (\A i \in Proc : i \in Corr => pc[i] # "AC")

(* An inductive invariant for the safety argument. *)
IndInv_Unforg == TypeOK /\ FCConstraints /\ sent = {} /\ pc = [ i \in Proc |-> "V0" ]

THEOREM InitNoBcast => IndInv_Unforg
  BY DEF InitNoBcast, Init, IndInv_Unforg

THEOREM IndInv_Unforg /\ [Next]_vars => IndInv_Unforg'
  <1>1 IndInv_Unforg' = TypeOK' /\ FCConstraints' /\ sent' = {} /\ pc' = [ i \in Proc |-> "V0" ]
       BY DEF IndInv_Unforg
  <1>2 IndInv_Unforg /\ UNCHANGED vars => IndInv_Unforg'
       <2>1 IndInv_Unforg /\ UNCHANGED vars => TypeOK' /\ FCConstraints'
          BY FCConstraints_TypeOK_Next DEF IndInv_Unforg
       <2>2 IndInv_Unforg /\ UNCHANGED vars => sent' = {} /\ pc' = [ i \in Proc |-> "V0" ]
          BY DEF IndInv_Unforg, vars
       <2> QED BY <2>1, <2>2
  <1>3 IndInv_Unforg /\ Next => IndInv_Unforg'
       <2> SUFFICES ASSUME TypeOK, FCConstraints, sent = {}, pc = [ i \in Proc |-> "V0" ],
                         (\E i \in Corr : Step(i)) \/ UNCHANGED vars
                         PROVE IndInv_Unforg'
                         BY DEF Step, Next, IndInv_Unforg
       <2>1 CASE UNCHANGED vars
            <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {},
                             pc = [ i \in Proc |-> "V0" ], UNCHANGED vars
                              PROVE IndInv_Unforg'
                              BY <2>1
            <3> QED BY <2>2
       <2>2 CASE \E i \in Corr : Step(i)
            <3> SUFFICES ASSUME TypeOK, FCConstraints, sent = {},
                             pc = [ i \in Proc |-> "V0" ], NEW i \in Corr, Step(i)
                             PROVE IndInv_Unforg'
                             BY <2>2
            <3>1 FCConstraints' /\ TypeOK'
                 BY FCConstraints_TypeOK_Next DEF IndInv_Unforg
            <3>2 sent' = {} /\ pc' = [ i \in Proc |-> "V0" ]
                 <4>1 Step(i) <=>
                       \/ ReceiveFromAny(i) /\ UponV1(i)
                       \/ ReceiveFromAny(i) /\ UponNonFaulty(i)
                       \/ ReceiveFromAny(i) /\ UponAcceptNotSent(i)
                       \/ ReceiveFromAny(i) /\ UponAcceptSent(i)
                       \/ ReceiveFromAny(i) /\ UNCHANGED << pc, sent, Corr, Faulty >>
                     BY DEF Step
                 <4>2 IndInv_Unforg /\ ReceiveFromAny(i) => Cardinality(rcvd'[i]) <= T
                      <5> SUFFICES ASSUME TypeOK, FCConstraints, sent = {},
                                    pc = [ i \in Proc |-> "V0" ], ReceiveFromAny(i)
                                    PROVE Cardinality(rcvd'[i]) <= T
                            <5>1 rcvd[i] \subseteq ByzMsgs
                                 BY DEF TypeOK
                            <5>2 rcvd[i] \subseteq sent \cup ByzMsgs
                                 BY <5>1, SET_SUBSET
                            <5>3 sent = {}
                                 OBVIOUS
                            <5>4 rcvd[i] \subseteq {}
                                 BY <5>2, <5>3, SUBSET_EMPTY
                            <5>5 rcvd'[i] \subseteq ByzMsgs
                                 <6>1 ReceiveFromAny(i) <=> Receive(i, TRUE)
                                      BY DEF ReceiveFromAny
                                 <6>2 (IF TRUE THEN ByzMsgs ELSE {}) = ByzMsgs
                                      OBVIOUS
                                 <6>3 Receive(i, TRUE) <=>
                                           \E newMessages \in SUBSET (sent \cup ByzMsgs) :
                                               rcvd' = [ j \in Proc |->
                                                          IF j = i THEN rcvd[i] \cup newMessages
                                                          ELSE rcvd[j] ]
                                      BY <6>2 DEF Receive
                                 <6>4 \E newMessages \in SUBSET ByzMsgs :
                                           rcvd' = [ j \in Proc |-
                                                      IF j = i THEN rcvd[i] \cup newMessages
                                                      ELSE rcvd[j] ]
                                      BY <5>3, <6>3
                                 <6>5 rcvd' = [ j \in Proc |->
                                                   IF j = i THEN rcvd[i] \cup newMessages
                                                   ELSE rcvd[j] ]
                                      BY <6>4
                                 <6>6 rcvd'[i] \subseteq rcvd[i] \cup ByzMsgs
                                      BY <6>5, SET_SUBSET
                                 <6> QED BY <5>3, <6>6, SET_SUBSET
                            <5>6 Cardinality(ByzMsgs) = Cardinality(Faulty)
                                 BY DEF FCConstraints
                            <5>7 Cardinality(Faulty) <= T
                                 BY DEF FCConstraints
                            <5>8 Cardinality(rcvd'[i]) <= Cardinality(ByzMsgs)
                                 <6>1 rcvd'[i] \in SUBSET ByzMsgs BY <5>5
                                 <6> QED BY <6>1, FS_Subset DEF FCConstraints
                            <5>9 QED BY <5>8, <5>6, <5>7, NTF
                      <4>3 (Cardinality(rcvd'[i]) <= T) =>
                           ~UponV1(i) /\ ~UponNonFaulty(i)
                           /\ ~UponAcceptNotSent(i) /\ ~UponAcceptSent(i)
                           /\ ~\E j \in Corr : Step(j)
                           /\ ~(\E j \in Corr : j # i /\ Step(j))
                           /\ ~(\E m \in M : Step(i) /\ << i, m >> \in sent)
                           /\ ~(\E j \in Corr : Step(j) /\ << i, "ECHO" >> \in sent)
                           /\ ~(\E j \in Corr : Step(j) /\ << j, "ECHO" >> \in sent)
                           /\ rcvd = rcvd'
                           /\ Corr = Corr' /\ Faulty = Faulty'
                           /\ pc = pc' /\ sent = sent'
                           <5>1 UponV1(i) =
                                 /\ pc[i] = "V1"
                                 /\ pc' = [ pc EXCEPT ![i] = "SE" ]
                                 /\ sent' = sent \cup { << i, "ECHO" >> }
                                 /\ UNCHANGED << Corr, Faulty >>
                                    BY DEF UponV1
                           <5>2 UponNonFaulty(i) =
                                 /\ pc[i] \notin { "V0", "V1" }
                                 /\ Cardinality(rcvd'[i]) >= N - 2 * T
                                 /\ Cardinality(rcvd'[i]) < N - T
                                 /\ pc' = [ pc EXCEPT ![i] = "SE" ]
                                 /\ sent' = sent \cup { << i, "ECHO" >> }
                                 /\ UNCHANGED << Corr, Faulty >>
                                    BY DEF UponNonFaulty
                           <5>3 UponAcceptNotSent(i) =
                                 /\ pc[i] \in { "V0", "V1" }
                                 /\ Cardinality(rcvd'[i]) >= N - T
                                 /\ pc' = [ pc EXCEPT ![i] = "AC" ]
                                 /\ sent' = sent \cup { << i, "ECHO" >> }
                                 /\ UNCHANGED << Corr, Faulty >>
                                    BY DEF UponAcceptNotSent
                           <5>4 UponAcceptSent(i) =
                                 /\ pc[i] = "SE"
                                 /\ Cardinality(rcvd'[i]) >= N - T
                                 /\ pc' = [ pc EXCEPT ![i] = "AC" ]
                                 /\ UNCHANGED << sent, Corr, Faulty >>
                                    BY DEF UponAcceptSent
                           <5>5 \E j \in Corr : Step(j) =>
                                    /\ rcvd[j] \subseteq rcvd[i]
                                    /\ pc[j] \notin { "V0", "V1" }
                                    /\ << j, "ECHO" >> \in sent
                                    /\ Cardinality(rcvd'[j]) >= N - 2 * T
                                    /\ CategorySubset(rcvd[i]) \in Cardinality(rcvd[i])
                                    /\ CategorySubset(rcvd'[j]) \in Cardinality(rcvd'[j])
                                    /\ (rcvd'[j] \subseteq rcvd[i] \cup ByzMsgs \/ ByzMsgs \subseteq rcvd'[j])
                                    /\ (rcvd[i] \subseteq rcvd'[j] \/ rcvd'[j] \subseteq rcvd[i])
                                    /\ (rcvd[i] \subseteq rcvd'[j] \/ rcvd'[j] \subseteq rcvd[i] \/ Cardinality(rcvd'[j]) < N - 2 * T)
                                    /\ (rcvd[i] \subseteq rcvd'[j] \/ rcvd'[j] \subseteq rcvd[i] \/ Cardinality(rcvd'[j]) < N - T)
                                    /\ (rcvd[i] \subseteq rcvd'[j] \/ rcvd'[j] \subseteq rcvd[i] \/ Cardinality(rcvd'[j]) >= N - T)
                                    /\ (\E m \in M : << i, m >> \in sent \/ << i, "ECHO" >> \in sent)
                                    /\ (\E m \in M : << j, m >> \in sent \/ << j, "ECHO" >> \in sent)
                                    /\ (\E j \in Corr : Step(j) /\ << i, "ECHO" >> \in sent)
                                    /\ (\E j \in Corr : Step(j) /\ << j, "ECHO" >> \in sent)
                                    /\ (\E j \in Corr : Step(j) /\ pc[j] \notin { "V0", "V1" })
                                    /\ (\E j \in Corr : Step(j) /\ Cardinality(rcvd'[j]) >= N - 2 * T)
                           BY SET_SUBSET, CategorySubset, DEF Step, Receive
                      <4> QED BY <4>1, <4>2, <4>3
            <3> QED BY <3>1, <3>2, <3>3
       <2> QED BY <2>1, <2>2
  <1> QED BY <1>2, <1>3

THEOREM IndInv_Unforg => Unforg
  <1>1 (\A i \in Proc : pc[i] = "V0") => (\A i \in Proc : pc[i] # "AC")
       BY SET_SUBSET
  <1>2 (\A i \in Proc : pc[i] = "V0") => (\A i \in Proc : pc[i] # "AC")
       BY DEF IndInv_Unforg
  <1> QED BY <1>2

THEOREM SpecNoBcast => []Unforg
  <1>1 InitNoBcast => IndInv_Unforg
       BY InitNoBcast, IndInv_Unforg
  <1>2 IndInv_Unforg /\ [][Next]_vars => IndInv_Unforg'
       BY IndInv_Unforg, Next
  <1>3 SpecNoBcast => []IndInv_Unforg
       BY <1>1, <1>2, PTL
  <1>4 IndInv_Unforg => Unforg
       BY IndInv_Unforg, Unforg
  <1> QED BY <1>3, <1>4, PTL

=============================================================================