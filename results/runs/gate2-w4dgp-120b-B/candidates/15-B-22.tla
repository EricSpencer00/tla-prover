------------------------------ MODULE bcastByz ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast distributed 
   algorithm with Byzantine faults.

   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:

   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94

   A short description of the parameterized model is described in:
   Gmeiner, Annu, et al. "Tutorial on parameterized model checking of fault
   tolerant distributed algorithms." International School on Formal Methods for
   the Design of Computer, Communication and Software Systems. Springer
   International Publishing, 2014.

   This specification has a TLAPS proof for property Unforgeability: if process p
   is correct and does not broadcast a message m, then no correct process ever
   accepts m.  The formula InitNoBcast represents that the transmitter does not
   broadcast any message.  So, we prove the formula
        (InitNoBcast /\ [][Next]_vars) => []Unforg

   We can use TLC to check two properties (for fixed parameters N, T, and F): the
   correctness property that if a correct process broadcasts, then every correct
   process accepts, and the replay property that if a correct process accepts,
   then every correct process accepts.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016

   This file is subject to the license bundled with this package, found in the
   file LICENSE.
 *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction,
        SequenceTheorems, TLAPS

CONSTANTS N, T, F
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T)
           /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == {"ECHO"}

ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* A correct process can receive all ECHO messages sent by correct processes
   and all ECHO messages from the Byzantine processes (if includeByz is TRUE). *)
Receive(self, includeByz) ==
  \E newm \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newm ]

UponV1(self) ==
  /\ pc[self] = "V1" /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponNonFaulty(self) ==
  /\ pc[self] \notin {"V0", "V1"} /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in {"V0", "V1"} /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup {<<self, "ECHO">>}
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE" /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(self) ==
  /\ Receive(self, TRUE)
  /\ \/ UponV1(self) \/ UponNonFaulty(self) \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next == (\E self \in Corr : Step(self)) \/ UNCHANGED vars
Spec == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars
Init ==
  /\ sent = {}
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [Proc -> {"V0"}] /\ Init

(* No forged broadcast: the only processes that accept are the broadcasters. *)
Unforge == (\A i \in Proc : i \in Corr => pc[i] # "AC")

(* Inductive invariant for FCConstraints/TypeOK and the no-broadcast case. *)
IndInvNoBcast ==
  /\ pc = [i \in Proc |-> "V0"]
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

TypeOK ==
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \X M
  /\ pc \in [Proc -> {"V0", "V1", "SE", "AC"}]
  /\ rcvd \in [Proc -> SUBSET (sent \cup ByzMsgs)]

UMFS_CardinalityType ==
  \A X, Y, Z \in SUBSET Nat :
    /\ X \cup Y = Z /\ X = Z \ Y
    => Cardinality(X) = Cardinality(Z) - Cardinality(Y)

NextStep ==
  \E self \in Corr :
    Receive(self, TRUE) /\ UponV1(self) /\ UNCHANGED << sent, Corr, Faulty >>
    \/ Receive(self, TRUE) /\ UponNonFaulty(self) /\ UNCHANGED << sent, Corr, Faulty >>
    \/ Receive(self, TRUE) /\ UponAcceptNotSentBefore(self) /\ UNCHANGED << Corr, Faulty >>
    \/ Receive(self, TRUE) /\ UponAcceptSentBefore(self) /\ UNCHANGED << Corr, Faulty >>
    \/ Receive(self, TRUE) /\ UNCHANGED << pc, sent, Corr, Faulty >>

SpecStep == Init /\ [NextStep]_vars

Liveness ==
  /\ Corr # {} /\ (\A i \in Corr : pc[i] = "V1")
  => <>(\A i \in Corr : pc[i] = "AC")

CorrLiveness ==
  (\A i \in Corr : pc[i] = "V1") => <>(\A i \in Corr : pc[i] = "AC")

ReplayLiveness ==
  []((\E i \in Corr: pc[i] = "AC") => <>(\A i \in Corr: pc[i] = "AC"))

=============================================================================