---- MODULE bcastByz ----
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

(* ------------------------------------------------------------------- *)
(*   Basic definitions                                                *)
(* ------------------------------------------------------------------- *)

Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* ------------------------------------------------------------------- *)
(*   Initial state                                                   *)
(* ------------------------------------------------------------------- *)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* ------------------------------------------------------------------- *)
(*   Receive actions                                                 *)
(* ------------------------------------------------------------------- *)

Receive(self, includeByz) ==
  \E newMessages \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup newMessages ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self) == Receive(self, TRUE)

(* ------------------------------------------------------------------- *)
(*   Process step actions                                            *)
(* ------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED <<Corr, Faulty, rcvd>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent
  /\ UNCHANGED <<Corr, Faulty>>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

(* ------------------------------------------------------------------- *)
(*   Safety invariant                                                *)
(* ------------------------------------------------------------------- *)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* ------------------------------------------------------------------- *)
(*   Unforgeability property                                         *)
(* ------------------------------------------------------------------- *)

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------- *)
(*   Theorem (safety)                                                *)
(* ------------------------------------------------------------------- *)

THEOREM SpecNoBcast => []Unforg

====