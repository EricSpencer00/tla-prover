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

\* Assumption about the parameters
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M

vars == <<pc, rcvd, sent, Corr, Faulty>>

(* Initial state: no messages sent, all processes start in V0, 
   Corr and Faulty are chosen nondeterministically but satisfy the cardinalities. *)
Init ==
  /\ pc \in [Proc -> {"V0","V1","SE","AC"}]
  /\ pc = [i \in Proc |-> "V0"]
  /\ sent = {}
  /\ rcvd = [i \in Proc |-> {}]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == Init /\ pc = [i \in Proc |-> "V0"]

(* Receive (possibly with Byzantine messages) *)
Receive(self, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [j \in Proc |-> IF j = self THEN rcvd[self] \cup new ELSE rcvd[j]]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty, rcvd>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty, rcvd>>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED <<Corr, Faulty, rcvd>>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED <<sent, Corr, Faulty, rcvd>>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(* Safety property: no correct process ever reaches the accepted state AC *)
Unforg == \A i \in Corr : pc[i] # "AC"

(* Inductive invariant used for the proof *)
IndInv_Unforg_NoBcast ==
  /\ pc = [i \in Proc |-> "V0"]
  /\ sent = {}
  /\ rcvd \in [Proc -> {}]   \* no messages have been received
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

=============================================================================