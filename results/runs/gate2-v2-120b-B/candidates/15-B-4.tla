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

Proc == 1 .. N
M == {"ECHO"}
ByzMsgs == Faulty \X M

VARIABLES Corr, Faulty, pc, rcvd, sent

vars == << Corr, Faulty, pc, rcvd, sent >>

Init ==
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr
  /\ pc \in [Proc -> {"V0", "V1"}]
  /\ rcvd = [i \in Proc |-> {}]
  /\ sent = {}

InitNoBcast ==
  /\ pc = [i \in Proc |-> "V0"]
  /\ Init

(* Receive any subset of sent ∪ ByzMsgs *)
Receive(self) ==
  \E new \in SUBSET (sent \cup ByzMsgs) :
     rcvd' = [j \in Proc |-> IF j = self THEN rcvd[self] \cup new ELSE rcvd[j]]

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - 2 * T
  /\ Cardinality(rcvd[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED << sent, Corr, Faulty, rcvd >>

Step(self) ==
  /\ Receive(self)
  /\ (UponV1(self) \/ UponNonFaulty(self) \/ UponAcceptNotSentBefore(self) \/ UponAcceptSentBefore(self)
      \/ UNCHANGED << pc, sent, Corr, Faulty >>)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

SpecNoBcast == InitNoBcast /\ [][Next]_vars

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* Minimal inductive invariant that guarantees Unforg *)
IndInv ==
  /\ pc = [i \in Proc |-> "V0"]
  /\ sent = {}
  /\ \A i \in Corr: i \in Proc
  /\ \A i \in Faulty: i \in Proc
  /\ Corr \subseteq Proc
  /\ Faulty = Proc \ Corr

THEOREM IndInvInit == InitNoBcast => IndInv
PROOF
  OBVIOUS
QED

THEOREM IndInvNext == IndInv /\ [Next]_vars => IndInv'
PROOF
  BY DEF Next, Step, IndInv, Receive, UponV1, UponNonFaulty,
     UponAcceptNotSentBefore, UponAcceptSentBefore
QED

THEOREM IndInvImpliesUnforg == IndInv => Unforg
PROOF
  ASSUME IndInv
  SHOW Unforg
  BY DEF Unforg, IndInv
QED

THEOREM SpecImpliesUnforg ==
  SpecNoBcast => []Unforg
PROOF
  USE SpecNoBcast, IndInvInit, IndInvNext, IndInvImpliesUnforg
  BY PTL
QED

======