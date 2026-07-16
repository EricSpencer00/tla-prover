---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
               (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M

vars == << Corr, Faulty, pc, rcvd, sent >>

(* ------------------------------------------------------------------------- *)
(* Initial state (no restriction on the values of pc)                        *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* ------------------------------------------------------------------------- *)
(* Initial state restricted to the unforgeability case (all correct processes
   start in V0).                                                             *)
InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* ------------------------------------------------------------------------- *)
(* Receive action (may receive messages from correct senders and optionally
   from Byzantine senders)                                                   *)
Receive(self, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup new
                                          ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)     == Receive(self, TRUE)

(* ------------------------------------------------------------------------- *)
(* Process steps (unchanged from the original specification)                  *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) <  N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self,"ECHO">> }
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty, rcvd >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ (UponV1(self) \/
      UponNonFaulty(self) \/
      UponAcceptNotSentBefore(self) \/
      UponAcceptSentBefore(self))

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(* Type invariant (unchanged)                                                 *)
TypeOK ==
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

(* ------------------------------------------------------------------------- *)
(* Safety invariant for unforgeability (unchanged)                            *)
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

=============================================================================