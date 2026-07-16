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

VARIABLES Corr, Faulty, pc, rcvd, sent

(*  The set of all processes.  *)
Proc == 1 .. N

(*  The set of possible Byzantine messages.  *)
M == {"ECHO"}
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(*  The original assumptions on the parameters.  The additional conjunct
    N - 2*T >= T + 1 is needed in the invariant proofs that rely on the
    bound T < N - 2*T.  It is consistent with the original NTF assumption. *)
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\
               (N > 3 * T) /\ (T >= F) /\ (F >= 0) /\ (N - 2*T >= T + 1)

(* -------------------------------------------------------------------------- *)
(*  Initial state                                                          *)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(*  A more restrictive initial state used for the Unforgeability property. *)
InitNoBcast ==
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* -------------------------------------------------------------------------- *)
(*  Receive actions                                                         *)

Receive(self, includeByz) ==
  \E new \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {} ) ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup new ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)       == Receive(self, TRUE)

(* -------------------------------------------------------------------------- *)
(*  Process step actions                                                    *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << rcvd, Corr, Faulty >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << rcvd, Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << rcvd, Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ UNCHANGED << sent, rcvd, Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ (UponV1(self)
      \/ UponNonFaulty(self)
      \/ UponAcceptNotSentBefore(self)
      \/ UponAcceptSentBefore(self)
      \/ UNCHANGED << pc, sent, Corr, Faulty >>)

(*  A transition of some correct process, or stuttering. *)
Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED vars

(* -------------------------------------------------------------------------- *)
(*  Full specifications                                                     *)

Spec        == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* -------------------------------------------------------------------------- *)
(*  Type correctness invariant (unchanged)                                   *)

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc

(* -------------------------------------------------------------------------- *)
(*  Cardinality (fault‑count) invariant                                      *)

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* -------------------------------------------------------------------------- *)
(*  Safety formula (Unforgeability)                                         *)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* -------------------------------------------------------------------------- *)
(*  The inductive invariant used for the safety proof                        *)

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

=============================================================================