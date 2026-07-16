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

(* -------------------------------------------------------------------------- *)
(* Assumptions about the parameters                                            *)
(* -------------------------------------------------------------------------- *)
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N               \* the set of all processes (including faulty ones)
M    == {"ECHO"}             \* the only message type
ByzMsgs == Faulty \X M       \* messages that can be forged by Byzantine processes

vars == << pc, rcvd, sent, Corr, Faulty >>

(* -------------------------------------------------------------------------- *)
(* Initialization                                                             *)
(* -------------------------------------------------------------------------- *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]                \* correct processes may start in either V0 or V1
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Special initial state for the unforgeability property *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* -------------------------------------------------------------------------- *)
(* Receive actions                                                            *)
(* -------------------------------------------------------------------------- *)
Receive(self, includeByz) ==
  \E new \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

(* -------------------------------------------------------------------------- *)
(* Process steps                                                              *)
(* -------------------------------------------------------------------------- *)
UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd[self] \cup {}) >= N - 2 * T
  /\ Cardinality(rcvd[self] \cup {}) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd[self] \cup {}) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd[self] \cup {}) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED << sent, Corr, Faulty, rcvd >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

(* -------------------------------------------------------------------------- *)
(* Next action                                                                *)
(* -------------------------------------------------------------------------- *)
Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

(* -------------------------------------------------------------------------- *)
(* Fairness and specifications                                                *)
(* -------------------------------------------------------------------------- *)
Spec ==
  Init /\ [][Next]_vars
    /\ WF_vars(\E self \in Corr: Step(self))

SpecNoBcast ==
  InitNoBcast /\ [][Next]_vars

(* -------------------------------------------------------------------------- *)
(* Type correctness invariant                                                 *)
(* -------------------------------------------------------------------------- *)
TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T

(* -------------------------------------------------------------------------- *)
(* Unforgeability safety property                                            *)
(* -------------------------------------------------------------------------- *)
Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* -------------------------------------------------------------------------- *)
(* Inductive invariant for the unforgeability proof                           *)
(* -------------------------------------------------------------------------- *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

=============================================================================