------------------------------ MODULE bcastByz ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast algorithm with Byzantine
   faults. It implements a one-round version of asynchronous reliable broadcast
   (Figure 7) from:

   T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive simple
   fault-tolerant algorithms. Distributed Computing 1987, 2(2):80--94.

   A short description of the parameterized model is given in
   Gmeiner et al. "Tutorial on parameterized model checking of fault-tolerant
   distributed algorithms" (2014). A TLAPS proof-showing that if a correct process
   does not broadcast a message then no correct process accepts it -- the
   unforgeability property -- is included.

   The model has a self-loop so the system always has a terminating computation.

   ByzMsgs == { <<p, "ECHO">> : p \in Faulty }: a set of Byzantine messages. *)
                  
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, NaturalsInduction,
        FiniteSetTheorems, TLAPS

CONSTANTS N, T, F

ASSUME N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M

vars == << pc, rcvd, sent, Corr, Faulty >>

(* A correct process may receive all ECHO messages sent by the other correct
   processes and all possible ECHO messages from the Byzantine ones; the
   includeByz flag toggles the Byzantine contribution. *)
Receive(self, includeByz) ==
  \E newMsgs \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i = self THEN rcvd[self] \cup newMsgs ELSE rcvd[i] ]

ReceiveFromCorrectSender(self) == Receive(self, FALSE)
ReceiveFromAnySender(self) == Receive(self, TRUE)

(* The broadcast algorithm from Figure 7 (Srikanth & Toueg). The first expression
   in each disjunction implements the corresponding step from the paper; the
   precondition |\in { "V0", "V1" } means the process has not broadcast yet. *)
Step(self) ==
  /\ ReceiveFromAnySender(self)
  /\ \/ /\ pc[self] = "V1"
        /\ pc' = [ pc EXCEPT ![self] = "SE" ]
        /\ sent' = sent \cup { <<self, "ECHO">> }
     \/ /\ pc[self] \notin { "V0", "V1" }
        /\ Cardinality(rcvd'[self]) >= N - 2 * T
        /\ Cardinality(rcvd'[self]) < N - T
        /\ pc' = [ pc EXCEPT ![self] = "SE" ]
        /\ sent' = sent \cup { <<self, "ECHO">> }
     \/ /\ pc[self] \in { "V0", "V1" }
        /\ Cardinality(rcvd'[self]) >= N - T
        /\ pc' = [ pc EXCEPT ![self] = "AC" ]
        /\ sent' = sent \cup { <<self, "ECHO">> }
     \/ /\ pc[self] = "SE"
        /\ Cardinality(rcvd'[self]) >= N - T
        /\ pc' = [ pc EXCEPT ![self] = "AC" ]
        /\ sent' = sent
     \/ UNCHANGED << pc, sent, Corr, Faulty >>

Init ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ sent = {}
  /\ Corr \subseteq Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) = N - F

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

Next == (\E self \in Corr : Step(self)) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
          /\ WF_vars(\E self \in Corr : /\ ReceiveFromCorrectSender(self)
                                   /\ \/ pc[self] = "V1" \/ Cardinality(rcvd'[self]) >= N - 2 * T
                                       \/ (pc[self] \in { "V0", "V1" } /\ Cardinality(rcvd'[self]) >= N - T)
                                       \/ (pc[self] = "SE" /\ Cardinality(rcvd'[self]) >= N - T)
                                       \/ UNCHANGED << pc, sent, Corr, Faulty >>)

SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd \in [ Proc -> SUBSET ( sent \cup ByzMsgs ) ]
  /\ sent \subseteq Proc \times M
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
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* The unforgeability case. *)
Unforg == \A i \in Proc : i \in Corr => (pc[i] # "AC")

(* Inductive invariant candidate for the unforgeability case. It is a
   strengthening of the empty-communicated and empty-sent conditions of
   InitNoBcast that makes the inductive step work. *)
IndInv_Unforg == TypeOK /\ FCConstraints /\ sent = {} /\ pc = [ i \in Proc |-> "V0" ]

UMFS_CardinalityType ==
  \A X, Y, Z : /\ IsFiniteSet(X) /\ IsFiniteSet(Y) /\ X \cup Y = Z /\ X = Z \ Y
                 => Cardinality(X) = Cardinality(Z) - Cardinality(Y)

\[IndInv_Unforg]_v ==
  /\ FCConstraints' /\ TypeOK' /\ sent' = {} /\ pc' = [ i \in Proc |-> "V0" ]
  /\ UNCHANGED << Corr, Faulty >>

(* The inductive invariant is satisfied by the initial state. *)
InitNoBcast => IndInv_Unforg

(* The invariant is preserved by the self-loop. *)
IndInv_Unforg /\ UNCHANGED vars => \[IndInv_Unforg]_v

(* The invariant is preserved by a broadcast step. *)
IndInv_Unforg /\ (\E i \in Corr : Step(i)) => \[IndInv_Unforg]_v

(* The invariant implies unforgeability. *)
IndInv_Unforg => Unforg

(* Therefore SpecNoBcast enforces unforgeability. *)
SpecNoBcast => []Unforg

====