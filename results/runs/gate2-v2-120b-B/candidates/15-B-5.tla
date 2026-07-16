---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0

Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M

VARIABLES Corr, Faulty, pc, rcvd, sent

vars == <<pc, rcvd, sent, Corr, Faulty>>

(* Initial state: no messages sent, each process either V0 or V1, no messages received,
   and the sets Corr and Faulty are a partition of Proc with |Corr| = N-F. *)
Init ==
  /\ sent = {}
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ rcvd = [i \in Proc |-> {}]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Subset of Init where every correct process starts in V0, used for the unforgeability
   line of the proof. *)
InitNoBcast == pc \in [Proc -> {"V0"}] /\ Init

(* A correct process may receive any subset of the union of all sent messages
   and the Byzantine messages. The parameter includeByz determines whether Byzantine
   messages are considered. *)
Receive(self, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [j \in Proc |-> IF j = self THEN rcvd[self] \cup new ELSE rcvd[j]]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)     == Receive(self, TRUE)

(* ------------------------------------------------------------------------- *)
(* Process actions                                                          *)
(* ------------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc'   = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty, rcvd>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc'   = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc'   = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc'   = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED <<Corr, Faulty>>

(* ------------------------------------------------------------------------- *)
(* Step definition                                                          *)
(* ------------------------------------------------------------------------- *)

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ (UponV1(self)
      \/ UponNonFaulty(self)
      \/ UponAcceptNotSentBefore(self)
      \/ UponAcceptSentBefore(self))
  /\ UNCHANGED Corr
  /\ UNCHANGED Faulty

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec ==
  Init /\ [][Next]_vars

SpecNoBcast ==
  InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Type correctness                                                         *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc

FCConstraints ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* ------------------------------------------------------------------------- *)
(* Safety property (unforgeability)                                         *)
(* ------------------------------------------------------------------------- *)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* ------------------------------------------------------------------------- *)
(* Inductive invariant (used only for TLC checking)                         *)
(* ------------------------------------------------------------------------- *)

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [i \in Proc |-> "V0"]

=============================================================================