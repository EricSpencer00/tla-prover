---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N                \* all processes
M == {"ECHO"}
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* Initial state: no messages sent, each process in V0 or V1, and a partition
   of the processes into correct (Corr) and faulty (Faulty). *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Special initial state for the unforgeability property: all correct
   processes start in V0. *)
InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* Receive allows a process to add any subset of the union of the messages
   already sent and, optionally, Byzantine messages. *)
Receive(self, includeByz) ==
  \E new \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {} ) ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)       == Receive(self, TRUE)

(* Process steps *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc'   = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) <  N - T
  /\ pc'   = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc'   = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc'   = [ pc EXCEPT ![self] = "AC" ]
  /\ UNCHANGED << sent, Corr, Faulty, rcvd >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ ( UponV1(self)
       \/ UponNonFaulty(self)
       \/ UponAcceptNotSentBefore(self)
       \/ UponAcceptSentBefore(self) )

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

(* Safety property: a correct process never reaches the accepted state. *)
Unforg == \A i \in Corr : pc[i] # "AC"

\* The invariant used by TLC
IndInv_Unforg_NoBcast ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ sent = {}
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ \A i \in Proc : pc[i] # "AC"

(* Temporal specification without fairness (safety only) *)
SpecNoBcast == InitNoBcast /\ [][Next]_vars

=============================================================================