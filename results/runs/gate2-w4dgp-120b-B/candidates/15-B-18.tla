------------------------------ MODULE bcastByz ------------------------------

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
   broadcast any message. So, we prove the formula (InitNoBcast /\ [][Next]_vars) => []Unforg                    
  
   We can use TLC to check two properties (for fixed parameters N, T, and F):
    - Correctness: if a correct process broadcasts, then every correct process accepts,
    - Replay: if a correct process accepts, then every correct process accepts.  
  
   Igor Konnov, Thanh Hai Tran, Josef Widder, 2016
  
   This file is a subject to the license that is bundled together with this package 
   and can be found in the file LICENSE.
 *)

EXTENDS Naturals, 
        FiniteSets,
        Functions,
        FunctionTheorems, 
        FiniteSetTheorems,
        NaturalsInduction,
        SequenceTheorems,
        TLAPS
        
CONSTANTS N, T, F

VARIABLES Corr           (* the correct processes *)
VARIABLES Faulty         (* the faulty processes *)
                         (* Corr and Faulty are declared as variables since we want to 
                           check all possible cases. After the initial step they never change. *)
VARIABLES pc             (* each process's control state *)
VARIABLES rcvd           (* the messages received by each process *)
VARIABLES sent           (* the messages sent by all correct processes *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
Vars == << Corr, Faulty, pc, rcvd, sent >>

(* Instead of modeling a broadcaster explicitly, two initial values V0 and V1 at correct
   processes are used to model whether a process has received the INIT message from the
   broadcaster. Then a correctness precondition can be modeled that all correct processes
   initially have V1, while the precondition of unforgeability is that they have V0.
 *)
Init == 
  /\ sent = {}
  /\ pc \in [ Proc -> {"V0", "V1"} ]
  /\ rcvd = [ i \in Proc |-> {} ]
  /\ Corr \in SUBSET Proc
  /\ Cardinality(Corr) = N - F
  /\ Faulty = Proc \ Corr  

(* The special case: all correct processes start at V0, i.e., none received an INIT. *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* A correct process receives any subset of correct messages and any subset of 
   Byzantine messages. *)
Receive(self, includeByz) ==
  \E newMessages \in SUBSET ( sent \cup (IF includeByz THEN ByzMsgs ELSE {}) ) :
    rcvd' = [ i \in Proc |-> IF i # self THEN rcvd[i] ELSE rcvd[self] \cup newMessages ]

ReceiveFromCorrect(i) == Receive(i, FALSE)
ReceiveFromAny(i) == Receive(i, TRUE)

(* Fig. 7 [1]: if p received an INIT and not yet sent, it sends ECHO to all. *)
UponV1(i) ==
  /\ pc[i] = "V1"
  /\ pc' = [pc EXCEPT ![i] = "SE"]
  /\ sent' = sent \cup { <<i, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* Fig. 7 [1]: if p (not V0/V1) received from >= N-2T correct processes and not yet sent, 
   it sends ECHO to all. *)
UponNonFaulty(i) ==
  /\ pc[i] \notin { "V0", "V1", "SE" }
  /\ Cardinality(rcvd'[i]) >= N - 2 * T
  /\ Cardinality(rcvd'[i]) < N - T
  /\ pc' = [ pc EXCEPT ![i] = "SE" ]
  /\ sent' = sent \cup { <<i, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* Fig. 7 [1]: if p received from >= N-T distinct processes and not yet sent, it accepts 
   and sends ECHO to all. *)
UponAcceptNotSent(i) ==
  /\ pc[i] \in { "V0", "V1" }
  /\ Cardinality(rcvd'[i]) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "AC" ]
  /\ sent' = sent \cup { <<i, "ECHO">> }
  /\ UNCHANGED << Corr, Faulty >>

(* Fig. 7 [1]: if p already sent and received from >= N-T, it accepts. *)
UponAcceptSent(i) ==
  /\ pc[i] = "SE"
  /\ Cardinality(rcvd'[i]) >= N - T
  /\ pc' = [ pc EXCEPT ![i] = "AC" ]
  /\ sent' = sent
  /\ UNCHANGED << Corr, Faulty >>

Step(i) == 
  /\ ReceiveFromAny(i)
  /\ \/ UponV1(i)
     \/ UponNonFaulty(i)
     \/ UponAcceptNotSent(i)
     \/ UponAcceptSent(i)

Next ==
  \/ \E i \in Corr : Step(i) \/ UNCHANGED Vars

Spec == Init /\ [][Next]_Vars /\ WF_Vars(\E i \in Corr: ReceiveFromCorrect(i) /\ 
                                          \/ UponV1(i) \/ UponNonFaulty(i) 
                                          \/ UponAcceptNotSent(i) \/ UponAcceptSent(i))
SpecNoBcast == InitNoBcast /\ [][Next]_Vars

(* Invariant for unforgeability: with no broadcast and no messages sent, no process is AC. *)
IndInv_Unforg ==
  /\ TypeOK
  /\ FCConstraints
  /\ sent = {}
  /\ pc = [ i \in Proc |-> "V0" ]

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
  /\ IsFiniteSet(ByzMsgs)
  /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

Unforg == (\A i \in Proc : i \in Corr => pc[i] # "AC")

THEOREM InitNoBcastImpliesIndInv ==
  InitNoBcast => IndInv_Unforg
  BY DEF IndInv_Unforg

THEOREM IndInvIsClosed ==
  IndInv_Unforg /\ [Next]_Vars => IndInv_Unforg'
  BY DEF IndInv_Unforg, Next

THEOREM IndInvImpliesUnforg ==
  IndInv_Unforg => Unforg
  BY DEF IndInv_Unforg

THEOREM SpecNoBcastImpliesUnforg ==
  SpecNoBcast => []Unforg
  BY InitNoBcastImpliesIndInv, IndInvIsClosed, IndInvImpliesUnforg, PTL

=============================================================================