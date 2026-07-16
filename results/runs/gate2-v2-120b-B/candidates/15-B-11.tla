---- MODULE bcastByz ----
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

(*---------------------------------------------------*)
(*   Helper definitions                              *)
(*---------------------------------------------------*)

Proc == 1 .. N               \* All processes, including the faulty ones
M == {"ECHO"}                \* Only one message type is used
ByzMsgs == Faulty \X M       \* Byzantine messages

vars == << pc, rcvd, sent, Corr, Faulty >>

(*---------------------------------------------------*)
(*   Initial predicate                              *)
(*---------------------------------------------------*)

Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(*---------------------------------------------------*)
(*   Receive action (any sender, may include byz)    *)
(*---------------------------------------------------*)

Receive(self) ==
  \E newMessages \in SUBSET ( sent \cup ByzMsgs ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup newMessages
                                      ELSE rcvd[i] ]

(*---------------------------------------------------*)
(*   Process steps                                   *)
(*---------------------------------------------------*)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty, rcvd >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - 2*T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"}
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) ==
  /\ Receive(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars

(*---------------------------------------------------*)
(*   Safety invariant (Unforgeability)              *)
(*---------------------------------------------------)

Unforg == \A i \in Proc : i \in Corr => pc[i] # "AC"

=============================================================================