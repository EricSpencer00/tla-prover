------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

(* ------------------------------------------------------------------------- *)
(*  Derived constants and sets                                               *)
(* ------------------------------------------------------------------------- *)

Proc == 1 .. N               \* All processes (including faulty ones)
M    == {"ECHO"}             \* The only message type
ByzMsgs == Faulty \X M       \* Byzantine messages

vars == << pc, rcvd, sent, Corr, Faulty >>

(* ------------------------------------------------------------------------- *)
(*  Safety assumptions (parameter constraints)                               *)
(* ------------------------------------------------------------------------- *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
               (N > 3 * T) /\ (T >= F) /\ (F >= 0)

(* ------------------------------------------------------------------------- *)
(*  Variables                                                                *)
(* ------------------------------------------------------------------------- *)

VARIABLE pc          \* control state of each process
VARIABLE rcvd        \* messages received by each process
VARIABLE sent        \* set of messages sent by correct processes
VARIABLE Corr        \* set of correct processes
VARIABLE Faulty      \* set of faulty processes

(* ------------------------------------------------------------------------- *)
(*  Initial state                                                           *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ sent = {}

(* Special initial state for the unforgeability property *)
InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* ------------------------------------------------------------------------- *)
(*  Helper action: receive a (possibly empty) set of messages                *)
(* ------------------------------------------------------------------------- *)

Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMessages
                                   ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

(* ------------------------------------------------------------------------- *)
(*  Process actions                                                         *)
(* ------------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

(* ------------------------------------------------------------------------- *)
(*  Combined step for a single correct process                              *)
(* ------------------------------------------------------------------------- *)

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

(* ------------------------------------------------------------------------- *)
(*  Global next action (only correct processes may act)                     *)
(* ------------------------------------------------------------------------- *)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

(* ------------------------------------------------------------------------- *)
(*  Specification (safety version)                                          *)
(* ------------------------------------------------------------------------- *)

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(*  Types (for debugging / TLC)                                             *)
(* ------------------------------------------------------------------------- *)

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* ------------------------------------------------------------------------- *)
(*  Cardinality constraints (used as an invariant)                         *)
(* ------------------------------------------------------------------------- *)

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
(*  Unforgeability safety property                                          *)
(* ------------------------------------------------------------------------- *)

Unforg == (\A i \in Proc : i \in Corr => pc[i] # "AC")

(* ------------------------------------------------------------------------- *)
(*  Intended inductive invariant (minimal, semantics‑preserving)           *)
(* ------------------------------------------------------------------------- *)

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

(* ------------------------------------------------------------------------- *)
(*  Liveness (not used for the safety check)                               *)
(* ------------------------------------------------------------------------- *)

Spec == SpecNoBcast /\ WF_vars(\E self \in Corr: Step(self))

=============================================================================