------------------------------ MODULE bcastByz ------------------------------

(* TLA+ encoding of a parameterized model of the broadcast algorithm with Byzantine faults.
  
   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:
  
   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive simple
   fault-tolerant algorithms. Distributed Computing 1987, Volume 2, Issue 2, pp 80-94
  
   A short description of the parameterized model is in Gmeiner, Annu, et al. "Tutorial on
   parameterized model checking of fault-tolerant distributed algorithms." ISFM'14.
  
   This specification has a TLAPS proof for unforgeability: if process p is correct and does
   not broadcast a message m, then no correct process ever accepts m. The safety goal is the
   formula (InitNoBcast /\ [][Next]_vars) => []Unforg.  The property Unforgeability below
   captures this when we start with InitNoBcast.

   The module also defines two TLC-checkable properties for fixed N,T,F:
     - Correctness: a correct broadcaster is accepted by every correct process.
     - Replay: if one correct process accepts, then every correct process accepts.

   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
 *)

EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems,
        FiniteSetTheorems, NaturalsInduction, SequenceTheorems, TLAPS

CONSTANTS N, T, F

VARIABLES Corr, Faulty, pc, rcvd, sent

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

(* The initial state models the case where no correct process receives an INIT message:
   every correct process has value V0 and the correct set may be any subset of size N-F. *)
Init == /\ sent = {}
        /\ pc \in [ Proc -> {"V0", "V1"} ]
        /\ rcvd = [ i \in Proc |-> {} ]
        /\ Corr \in SUBSET Proc
        /\ Cardinality(Corr) = N - F
        /\ Faulty = Proc \ Corr

InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* A correct process can receive all ECHO messages from the other correct processes
   (a subset of sent) and all possible ECHO messages from the Byzantine ones (a subset of
   ByzMsgs). ByzMsgs is empty when there are no Byzantine processes. *)
Receive(self, byz) ==
  \E newMess \in SUBSET (sent \cup (IF byz THEN ByzMsgs ELSE {})) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMess ]

ReceiveFromCorrect(i) == Receive(i, FALSE)
ReceiveFromAny(i)     == Receive(i, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [ pc EXCEPT ![self] = "SE" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [ pc EXCEPT ![self] = "AC" ]
  /\ UNCHANGED << sent, Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAny(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next == \/ \E self \in Corr: Step(self) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK == /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
          /\ Corr \subseteq Proc
          /\ Faulty \subseteq Proc
          /\ sent \subseteq Proc \X M
          /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

Unforgeability == (\A i \in Proc : i \in Corr => (pc[i] # "AC"))

Unforg == (\A i \in Proc : i \in Corr => (pc[i] # "AC"))

(* An inductive invariant that establishes Unforgeability with InitNoBcast: no messages
   ever sent and all processes stuck at V0.  The constraints between the number of messages,
   pc, and the number of faulty processes below are the extra ingredients that make the
   invariant inductive. *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

THEOREM InitNoBcast => IndInv_Unforg_NoBcast
  BY DEF InitNoBcast, Init, IndInv_Unforg_NoBcast

THEOREM IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  BY DEF IndInv_Unforg_NoBcast, Next, Step, Receive

THEOREM IndInv_Unforg_NoBcast => Unforg
  BY DEF IndInv_Unforg_NoBcast, Unforg

THEOREM SpecNoBcast => []Unforg
  BY PTL DEF SpecNoBcast, IndInv_Unforg_NoBcast, Unforg

(* If a correct process broadcasts, every correct process eventually accepts it. *)
CorrLtl == (\A i \in Corr : pc[i] = "V1") => <>(\A i \in Corr : pc[i] = "AC")

(* If one correct process accepts, every correct process accepts. *)
RelayLtl == []((\E i \in Corr : pc[i] = "AC") => <>(\A i \in Corr : pc[i] = "AC"))

====