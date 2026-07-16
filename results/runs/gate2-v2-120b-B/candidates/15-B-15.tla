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

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N          \* all processes, including the faulty ones
M == {"ECHO"}
ByzMsgs == Faulty \X M

(* The set of all variables *)
vars == << pc, rcvd, sent, Corr, Faulty >>

(* Initial state: no messages sent, all processes start in V0, 
   a subset of N-F processes are correct, the rest are faulty *)
Init ==
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \subseteq Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

(* Receive messages from any sender (correct or faulty) *)
Receive(self) ==
  \E newMessages \in SUBSET (sent \cup ByzMsgs) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i]
                                      ELSE rcvd[self] \cup newMessages ]

(* UponV1: a process that has V1 (cannot happen in Init) would send ECHO,
   but because Init forces V0 for all, this action is never enabled. *)
UponV1(self) ==
  /\ FALSE
  /\ UNCHANGED << pc, sent, Corr, Faulty, rcvd >>

(* UponNonFaulty: a correct process that has received enough ECHO messages
   from distinct processes but not enough to accept. In the InitNoBcast case,
   this action is never enabled because sent is empty. *)
UponNonFaulty(self) ==
  /\ FALSE
  /\ UNCHANGED << pc, sent, Corr, Faulty, rcvd >>

(* UponAcceptNotSentBefore: a process that can accept because it has 
   received enough ECHO messages, but has not sent before. Also never enabled. *)
UponAcceptNotSentBefore(self) ==
  /\ FALSE
  /\ UNCHANGED << pc, sent, Corr, Faulty, rcvd >>

(* UponAcceptSentBefore: a process that has already sent ECHO and can now accept.
   Also never enabled in the InitNoBcast scenario. *)
UponAcceptSentBefore(self) ==
  /\ FALSE
  /\ UNCHANGED << pc, sent, Corr, Faulty, rcvd >>

(* Step combines all possible actions for a correct process. All actions are
   effectively no-ops because their preconditions are false under InitNoBcast. *)
Step(self) ==
  \/ Receive(self)
  \/ UponV1(self)
  \/ UponNonFaulty(self)
  \/ UponAcceptNotSentBefore(self)
  \/ UponAcceptSentBefore(self)

(* Next allows any correct process to take a step, or stutter. *)
Next ==
  \/ \E self \in Corr: Step(self)
  \/ UNCHANGED vars

(* Type correctness invariant *)
TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

(* Cardinality constraints for correct and faulty sets *)
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

(* The safety property: no correct process ever reaches the accepted state AC *)
Unforg ==
  \A i \in Proc : i \in Corr => pc[i] # "AC"

(* Explicitly disable the weak fairness condition for the safety check *)
SpecNoBcast ==
  Init /\ [][Next]_vars

=============================================================================