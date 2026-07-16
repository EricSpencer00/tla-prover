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

VARIABLE Corr           \* the correct processes
VARIABLE Faulty         \* the faulty processes
VARIABLE pc             \* the control state of each process
VARIABLE rcvd           \* the messages received by each process
VARIABLE sent           \* the messages sent by all correct processes

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N          \* all processes, including the faulty ones
M == {"ECHO"}
ByzMsgs == Faulty \X M

vars == <<pc, rcvd, sent, Corr, Faulty>>

Init ==
  /\ sent = {}
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ rcvd = [i \in Proc |-> {}]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [Proc -> {"V0"}] /\ Init

(* Message receive, possibly including Byzantine messages *)
Receive(self, includeByz) ==
  \E newMsg \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [i \in Proc |-> IF i = self THEN rcvd[i] \cup newMsg ELSE rcvd[i]]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)       == Receive(self, TRUE)

(* Process steps *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc'   = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) <  N - T
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

(* Safety invariant: no correct process ever accepts a message *)
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* Minimal inductive invariant that implies Unforg *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ sent = {}
  /\ pc = [i \in Proc |-> "V0"]

TypeOK ==
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]

(* Proof obligations are expressed as theorems but are not needed for model checking *)

====