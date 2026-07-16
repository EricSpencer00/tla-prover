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

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N          \* all processes, including the faulty ones
M    == {"ECHO"}

VARIABLES Corr, Faulty, pc, rcvd, sent

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
ByzMsgs == Faulty \X M   \* messages that may be forged by Byzantine processes

vars == << pc, rcvd, sent, Corr, Faulty >>

(* ------------------------------------------------------------------------- *)
(* Initial predicate (unrestricted)                                         *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Special initial predicate used for the unforgeability property                *)
InitNoBcast == 
  /\ pc \in [ Proc -> {"V0"} ]
  /\ sent = {}
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* ------------------------------------------------------------------------- *)
(* Actions                                                                  *)

Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup newMessages ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)     == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty, rcvd >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)
     \/ UNCHANGED << pc, sent, Corr, Faulty >>

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Type correctness invariant                                               *)
TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* ------------------------------------------------------------------------- *)
(* Cardinality constraints (used as an invariant)                           *)
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

(* ------------------------------------------------------------------------- *)
(* Safety property: unforgeability                                          *)
Unforg == (\A i \in Proc : i \in Corr => pc[i] # "AC")

(* ------------------------------------------------------------------------- *)
(* Full invariant used for model checking                                    *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ rcvd = [ i \in Proc |-> {} ]

=============================================================================