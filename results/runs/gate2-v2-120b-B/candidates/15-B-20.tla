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

(* ------------------------------------------------------------------------- *)
(*   Helper definitions                                                    *)
(* ------------------------------------------------------------------------- *)

Proc == 1 .. N                \* All processes, including the faulty ones
M    == {"ECHO"}              \* The only message type used
ByzMsgs == Faulty \X M        \* Byzantine messages

vars == << pc, rcvd, sent, Corr, Faulty >>

TypeOK ==
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]

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

(* ------------------------------------------------------------------------- *)
(*   Initial predicate                                                     *)
(* ------------------------------------------------------------------------- *)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0","V1","SE","AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == 
  /\ pc \in [ Proc -> {"V0"} ]
  /\ Init

(* ------------------------------------------------------------------------- *)
(*   Receive actions                                                       *)
(* ------------------------------------------------------------------------- *)

Receive(self, includeByz) ==
  \E newMessages \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[i] \cup newMessages ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self)      == Receive(self, TRUE)

(* ------------------------------------------------------------------------- *)
(*   Process steps (the only actions that change state)                     *)
(* ------------------------------------------------------------------------- *)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self,"ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self,"ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0","V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self,"ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty, rcvd >>

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

SpecNoBcast == InitNoBcast /\ [][Next]_vars

(* ------------------------------------------------------------------------- *)
(*   Invariant (strengthened to make the model check)                        *)
(* ------------------------------------------------------------------------- *)

IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

(* ------------------------------------------------------------------------- *)
(*   Safety property (Unforgeability)                                      *)
(* ------------------------------------------------------------------------- *)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

=============================================================================