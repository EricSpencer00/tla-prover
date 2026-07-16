------------------------------ MODULE bcastByz ------------------------------

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

(* ------------------------------------------------------------------------- *)
(* Assumptions about the parameters                                            *)
(* ------------------------------------------------------------------------- *)
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
               (N > 3 * T) /\ (T >= F) /\ (F >= 0) /\ (N - 2*T >= T + 1)

Proc == 1 .. N               \* All processes
M == {"ECHO"}                \* Message type
ByzMsgs == Faulty \X M        \* Byzantine messages

vars == << Corr, Faulty, pc, rcvd, sent >>

(* ------------------------------------------------------------------------- *)
(* Initial state                                                            *)
(* ------------------------------------------------------------------------- *)
Init ==
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]

(* The special initial state for the unforgeability property: no process
   ever receives an INIT message. *)
InitNoBcast ==
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]

(* ------------------------------------------------------------------------- *)
(* Helper actions                                                            *)
(* ------------------------------------------------------------------------- *)

(* A process receives any subset of the messages that have been sent,
   possibly also Byzantine messages. *)
Receive(self, includeByz) ==
  \E new \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {} ) ) :
    /\ rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

(* ------------------------------------------------------------------------- *)
(* Process steps                                                            *)
(* ------------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - 2*T
  /\ Cardinality(rcvd[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ UNCHANGED << Corr, Faulty, sent, rcvd >>

(* A correct process may execute any of the above actions, each prefixed
   with a receive step. *)
Step(self) ==
  \/ ReceiveFromAnySender(self) /\ UponV1(self)
  \/ ReceiveFromAnySender(self) /\ UponNonFaulty(self)
  \/ ReceiveFromAnySender(self) /\ UponAcceptNotSentBefore(self)
  \/ ReceiveFromAnySender(self) /\ UponAcceptSentBefore(self)
  \/ ReceiveFromAnySender(self) /\ UNCHANGED << pc, sent, Corr, Faulty >>

(* ------------------------------------------------------------------------- *)
(* Global transition relation                                                *)
(* ------------------------------------------------------------------------- *)
Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec ==
  Init /\ [][Next]_vars

SpecNoBcast ==
  InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Type invariant                                                            *)
(* ------------------------------------------------------------------------- *)
TypeOK ==
  /\ Corr \subseteq Proc
  /\ Faulty = Proc \ Corr
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* ------------------------------------------------------------------------- *)
(* Unforgeability invariant (the safety property)                           *)
(* ------------------------------------------------------------------------- *)
Unforg ==
  \A i \in Proc : i \in Corr => pc[i] # "AC"

(* ------------------------------------------------------------------------- *)
(* Inductive invariant used for the safety proof                            *)
(* ------------------------------------------------------------------------- *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

=============================================================================