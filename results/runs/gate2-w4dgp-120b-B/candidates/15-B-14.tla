---- MODULE bcastByz ----
(* TLA+ encoding of a parameterized model of the broadcast distributed  
   algorithm with Byzantine faults.
  
   This is a one-round version of asynchronous reliable broadcast (Fig. 7) from:
  
   [1] T. K. Srikanth, Sam Toueg. Simulating authenticated broadcasts to derive
   simple fault-tolerant algorithms. Distributed Computing 1987,
   Volume 2, Issue 2, pp 80-94
                                                             
   A short description of the parameterized model is described in: Gmeiner,   
   Annu, et al. "Tutorial on parameterized model checking of fault-tolerant   
   distributed algorithms." International School on Formal Methods for the  
   Design of Computer, Communication and Software Systems. Springer  
   International Publishing, 2014.                   
  
   This specification has a TLAPS proof for property Unforgeability: if process p 
   is correct and does not broadcast a message m, then no correct process ever 
   accepts m. The formula InitNoBcast represents that the transmitter does not 
   broadcast any message. So, our goal is to prove the  formula
        (InitNoBcast /\ [][Next]_vars) => []Unforg                    
  
   We can use TLC to check two properties (for fixed parameters N, T, and F):
    - Correctness: if a correct process broadcasts, then every correct process accepts,
    - Replay: if a correct process accepts, then every correct process accepts.  
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
 *)
EXTENDS Naturals, FiniteSets, Functions, FunctionTheorems, NatSetTheory, TLAPS
CONSTANTS N, T, F
ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs ==  Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>

(* Instead of modeling a broadcaster directly, two initial values V0 and V1 at correct
   processes are used to model whether a process has received the INIT message from
   a broadcaster or not. This way the condition "no correct process broadcast" can be
   modeled as "all correct processes have value V0".
 *)
Init == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr

InitNoBcast == pc = [ i \in Proc |-> "V0" ] /\ Init

Receive(self, includeByz) ==
  \E m \in SUBSET (sent \cup (IF includeByz THEN ByzMsgs ELSE {})):
    rcvd' = [ i \in Proc |->
                IF i # self THEN rcvd[i] ELSE rcvd[self] \cup m ]

ReceiveFromCorrect(self) == Receive(self, FALSE)
ReceiveFromAny(self) == Receive(self, TRUE)

UponV1(self) ==
  /\ pc[self] = "V1"
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponNonFaulty(self) ==
  /\ pc[self] \notin { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - 2 * T
  /\ Cardinality(rcvd'[self]) < N - T
  /\ pc' = [pc EXCEPT ![self] = "SE"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptNotSentBefore(self) ==
  /\ pc[self] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ sent' = sent \cup { <<self, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

UponAcceptSentBefore(self) ==
  /\ pc[self] = "SE"
  /\ Cardinality(rcvd'[self]) >= N - T
  /\ pc' = [pc EXCEPT ![self] = "AC"]
  /\ UNCHANGED << sent, Corr, Faulty >>

Step(self) ==
  /\ ReceiveFromAny(self)
  /\ \/ UponV1(self)
     \/ UponNonFaulty(self)
     \/ UponAcceptNotSentBefore(self)
     \/ UponAcceptSentBefore(self)

Next == (\E self \in Corr: Step(self)) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
SpecNoBcast == InitNoBcast /\ [][Next]_vars

TypeOK ==
  /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
  /\ Corr \subseteq Proc
  /\ Faulty \subseteq Proc
  /\ sent \subseteq Proc \times M
  /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

FCConstraints ==
  /\ Corr \cup Faulty = Proc
  /\ Faulty = Proc \ Corr
  /\ Cardinality(Corr) >= N - T
  /\ Cardinality(Faulty) <= T
  /\ ByzMsgs \subseteq Proc \X M
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* An inductive invariant used only for the unforgeability check. *)
IndInv_Unforg_NoBcast ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

Unforg == (\A i \in Proc : i \in Corr => pc[i] # "AC")

THEOREM UnforgStep1 == InitNoBcast => IndInv_Unforg_NoBcast
  BY DEF InitNoBcast, IndInv_Unforg_NoBcast
THEOREM UnforgStep2 ==
  IndInv_Unforg_NoBcast /\ [Next]_vars => IndInv_Unforg_NoBcast'
  BY DEF IndInv_Unforg_NoBcast, Next, Step
THEOREM UnforgStep3 == IndInv_Unforg_NoBcast => Unforg
  BY DEF IndInv_Unforg_NoBcast, Unforg
THEOREM UnforgStep4 == SpecNoBcast => []Unforg
  BY <1>1, <1>2, <1>3, PTL DEF SpecNoBcast

=============================================================================