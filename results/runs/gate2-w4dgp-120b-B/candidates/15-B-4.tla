---- MODULE bcastByz
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, FiniteSetTheorems,
        NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ N > 3 * T /\ T >= F

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

\* Correctness is modeled by two values: V0 for processes that didn't receive the
\* INIT message from the broadcaster, and V1 for those that did.
Init == /\ sent = {}
        /\ pc \in [ Proc -> {"V0", "V1"} ]
        /\ rcvd = [ i \in Proc |-> {} ]
        /\ Corr \in SUBSET Proc /\ Cardinality(Corr) = N - F
        /\ Faulty = Proc \ Corr

(* No broadcast: all correct processes start in V0. *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

\* A correct process receives all ECHO messages from correct processes, and any
\* subset of Byzantine messages (determined by includeByz).
Receive(self, includeByz) ==
  \E newMessages \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]

ReceiveFromCorrect(self) == Receive(self, FALSE)
ReceiveFromAny(self) == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1" /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> } /\ UNCHANGED <<Corr, Faulty>>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"} /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> } /\ UNCHANGED <<Corr, Faulty>>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"} /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> } /\ UNCHANGED <<Corr, Faulty>>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE" /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent /\ UNCHANGED <<Corr, Faulty>>

Step(c) == ReceiveFromAny(c) /\ (UponV1(c) \/ UponNonFaulty(c)
                 \/ UponAcceptNotSentBefore(c) \/ UponAcceptSentBefore(c))
             \/ UNCHANGED vars

Next == \/ \E c \in Corr : Step(c) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
          /\ WF_vars(\E c \in Corr : ReceiveFromCorrect(c) /\ (UponV1(c) \/ UponNonFaulty(c)
                 \/ UponAcceptNotSentBefore(c) \/ UponAcceptSentBefore(c)))

SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK == pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ] /\ Corr \subseteq Proc
          /\ Faulty \subseteq Proc /\ sent \subseteq Proc \X M
          /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

(\* No broadcast: a correct process stays at V0 and never accepts. \*)
Unforgeable == (\A i \in Proc : i \in Corr => (pc[i] /= "AC"))

\* Unforgeability is an inductive invariant of SpecNoBcast.
IndInv == /- TypeOK /\ sent = {} /\ pc = [ i \in Proc |-> "V0" ]

InitNoBcast => IndInv
IndInv /\ [Next]_vars => IndInv' /\ TypeOK'
SpecNoBcast => []Unforgeable

=============================================================================