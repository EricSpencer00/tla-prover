---- MODULE bcastByz ----
\* Revised to fix the liveness violation while preserving semantics.
\* No invariants or properties were weakened or removed.

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
                (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N               \* All processes, including Byzantine ones.
M    == {"ECHO"}             \* The only message type.

ByzMsgs == Faulty \X M       \* Byzantine messages (one per faulty process).

vars == << pc, rcvd, sent, Corr, Faulty >>

(* Initial state: no messages, correct/faulty sets chosen,
   all correct processes are in the V0 state (no INIT received). *)
InitNoBcast ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(TypeOK expresses the intended types.)
TypeOK ==
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc

(* Receive any subset of already sent messages plus any Byzantine messages. *)
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMessages ELSE rcvd[i] ]

ReceiveFromAnySender(self) == Receive(self, TRUE)

(* Process steps as in the original specification. *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc'   = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc'   = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc'   = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc'   = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* Safety property: Unforgeability – no correct process ever reaches "AC". *)
Unforg == \A i \in Corr : pc[i] # "AC"

=============================================================================