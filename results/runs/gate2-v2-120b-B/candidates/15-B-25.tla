---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction, SequenceTheorems,
        TLAPS, Integers, Folds, WellFoundedInduction, Sequences

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

(* ------------------------------------------------------------------------- *)
(* Helper definitions                                                       *)
(* ------------------------------------------------------------------------- *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
               (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M    == {"ECHO"}
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* ------------------------------------------------------------------------- *)
(* Initial predicate                                                        *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* A more restricted initial predicate used for the unforgeability theorem. *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* ------------------------------------------------------------------------- *)
(* Receive actions                                                          *)
(* ------------------------------------------------------------------------- *)

Receive(self, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

(* ------------------------------------------------------------------------- *)
(* Process steps                                                            *)
(* ------------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - 2 * T
  /\ Cardinality(rcvd[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED << sent, Corr, Faulty, rcvd >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ (   UponV1(self)
      \/ UponNonFaulty(self)
      \/ UponAcceptNotSentBefore(self)
      \/ UponAcceptSentBefore(self) )

(* ------------------------------------------------------------------------- *)
(* Next action (unfair, used for the safety part)                           *)
(* ------------------------------------------------------------------------- *)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Safety invariant (unforgeability)                                         *)
(* ------------------------------------------------------------------------- *)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* ------------------------------------------------------------------------- *)
(* Inductive invariant used by the model checker                             *)
(* ------------------------------------------------------------------------- *)

IndInv_Unforg_NoBcast ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ sent = {}
  /\ \A i \in Proc : pc[i] # "AC"

(* ------------------------------------------------------------------------- *)
(* Specification used for TLC (includes the inductive invariant)            *)
(* ------------------------------------------------------------------------- *)

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Theorem (for TLC)                                                       *)
(* ------------------------------------------------------------------------- *)

THEOREM SpecNoBcast => []Unforg

=============================================================================