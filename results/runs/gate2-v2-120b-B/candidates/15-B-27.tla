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

(* ------------------------------------------------------------------- *)
(*  Derived constants and sets                                          *)
(* ------------------------------------------------------------------- *)

Proc == 1 .. N          (* All processes, including faulty ones *)
M    == {"ECHO"}        (* The only message type used *)
ByzMsgs == Faulty \X M  (* Byzantine messages *)

vars == << pc, rcvd, sent, Corr, Faulty >>

(* ------------------------------------------------------------------- *)
(*  Initial state (unrestricted)                                       *)
(* ------------------------------------------------------------------- *)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* ------------------------------------------------------------------- *)
(*  Restricted initial state used for the unforgeability theorem       *)
(* ------------------------------------------------------------------- *)

InitNoBcast == 
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* ------------------------------------------------------------------- *)
(*  Receive action (may receive from correct and Byzantine senders)    *)
(* ------------------------------------------------------------------- *)

Receive(self, includeByz) ==
  \E newMsgs \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMsgs ELSE rcvd[i] ]

ReceiveFromCorrect(self) == Receive(self, FALSE)
ReceiveFromAnySender(self) == Receive(self, TRUE)

(* ------------------------------------------------------------------- *)
(*  Process steps                                                     *)
(* ------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd[self]) >= N - 2*T
  /\ Cardinality(rcvd[self]) <  N - T
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
  /\ ReceiveFromAnySender(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

(* ------------------------------------------------------------------- *)
(*  Next relation (only correct processes may act)                     *)
(* ------------------------------------------------------------------- *)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

(* ------------------------------------------------------------------- *)
(*  Full specifications                                                *)
(* ------------------------------------------------------------------- *)

Spec      == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------- *)
(*  Safety property (Unforgeability)                                   *)
(* ------------------------------------------------------------------- *)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

(* ------------------------------------------------------------------- *)
(*  Inductive invariant used for the proof                             *)
(* ------------------------------------------------------------------- *)

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

(* ------------------------------------------------------------------- *)
(*  Type correctness definition                                        *)
(* ------------------------------------------------------------------- *)

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

(* ------------------------------------------------------------------- *)
(*  Cardinality constraints (invariant)                                *)
(* ------------------------------------------------------------------- *)

FCConstraints ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ IsFiniteSet(Corr)
  /\ IsFiniteSet(Faulty)
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* ------------------------------------------------------------------- *)
(*  Theorem statement for TLAPS                                        *)
(* ------------------------------------------------------------------- *)

THEOREM SpecNoBcast => []Unforg

====