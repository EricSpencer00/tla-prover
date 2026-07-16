---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
               (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* Initial state: no messages sent, each process in V0 or V1,  
   Corr and Faulty are chosen nondeterministically but satisfy the
   cardinality constraints. *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Restricted initial state used for the Unforgeability property. *)
InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* Receive messages from any sender (correct or Byzantine). *)
Receive(self, includeByz) ==
  \E newMsgs \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMsgs ELSE rcvd[i] ]

ReceiveFromAnySender(self) == Receive(self, TRUE)

(* Transition actions. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ (UponV1(self) \/
      UponNonFaulty(self) \/
      UponAcceptNotSentBefore(self) \/
      UponAcceptSentBefore(self))

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* Safety property: no correct process ever reaches the accepted state. *)
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* Minimal inductive invariant needed for the proof. *)
IndInv_Unforg_NoBcast ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ sent = {}
  /\ rcvd \in [ Proc -> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr

=============================================================================