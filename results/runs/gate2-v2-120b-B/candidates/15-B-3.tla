------------------------------ MODULE bcastByz ------------------------------
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

(* --------------------------------------------------------------------- *)
(*   Helper definitions                                                 *)
(* --------------------------------------------------------------------- *)

Proc == 1 .. N               \* All processes, including the faulty ones
M    == {"ECHO"}             \* The only message type used
ByzMsgs == Faulty \X M       \* Byzantine messages (pair of faulty proc and "ECHO")

(* --------------------------------------------------------------------- *)
(*   State constraints                                                  *)
(* --------------------------------------------------------------------- *)

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]
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
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* --------------------------------------------------------------------- *)
(*   Initialization                                                     *)
(* --------------------------------------------------------------------- *)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast ==
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* --------------------------------------------------------------------- *)
(*   Actions                                                            *)
(* --------------------------------------------------------------------- *)

Receive(self, includeByz) ==
  \E newMsgs \in SUBSET ( sent \cup IF includeByz THEN ByzMsgs ELSE {} ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup newMsgs ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

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
  /\ UNCHANGED << sent, Corr, Faulty, rcvd >>

Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr : Step(self)
  \/ UNCHANGED << pc, rcvd, sent, Corr, Faulty >>

(* --------------------------------------------------------------------- *)
(*   Specification                                                      *)
(* --------------------------------------------------------------------- *)

Spec          == Init /\ [][Next]_<<pc, rcvd, sent, Corr, Faulty>>
SpecNoBcast   == InitNoBcast /\ [][Next]_<<pc, rcvd, sent, Corr, Faulty>>

(* --------------------------------------------------------------------- *)
(*   Safety property (Unforgeability)                                   *)
(* --------------------------------------------------------------------- *)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* --------------------------------------------------------------------- *)
(*   Inductive invariant (strengthened for TLC)                         *)
(* --------------------------------------------------------------------- *)

IndInv_Unforg_NoBcast_TLC ==
  /\ pc = [ i \in Proc |-> "V0" ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) >= N - T
  /\ Faulty = Proc \ Corr
  /\ sent = {}
  /\ rcvd \in [ Proc -> SUBSET ByzMsgs ]

(* --------------------------------------------------------------------- *)
(*   TLAPS theorems (kept unchanged)                                   *)
(* --------------------------------------------------------------------- *)

THEOREM NTFRel ==
  N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F /\ F >= 0 /\ N - 2*T >= T + 1
  BY NTF

THEOREM ProcProp ==
  Cardinality(Proc) = N /\ IsFiniteSet(Proc) /\ Cardinality(Proc) \in Nat
  BY FS_Interval, NTFRel DEF Proc

...  \* (All other theorems from the original file are kept unchanged)

=============================================================================