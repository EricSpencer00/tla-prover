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
   broadcast any message. So, we prove the  formula
        (InitNoBcast /\ [][Next]_vars) => []Unforg                    
  
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

VARIABLES Corr, Faulty,  (* the correct and faulty processes: these are declared as 
                            variables so we consider all possible cases, then they stop
                            changing after Init.  *)
          pc, rcvd, sent    (* the control state of each process, the messages received
                               by each process, and the messages all correct processes
                               have sent. *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat
              /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
M == { "ECHO" }
ByzMsgs == Faulty \X M
vars == << pc, rcvd, sent, Corr, Faulty >>


Init == /\ sent = {}
        /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
        /\ rcvd = [ i \in Proc |-> {} ]
        /\ Corr \in SUBSET Proc
        /\ Cardinality(Corr) = N - F
        /\ Faulty = Proc \ Corr

(* The special case: all correct processes start in the local state V0, i.e.,
   none received an INIT message from a broadcaster.  *)
InitNoBcast == pc \in [ Proc -> {"V0"} ] /\ Init

(* A correct process receives any subset of the correct processes' ECHO messages,
   plus any subset of the Byzantine processes' ECHO messages. *)
ReceiveFromCorrect(i) ==
  \E S \subseteq sent : rcvd' = [ rcvd EXCEPT ![i] = rcvd[i] \cup S ]
ReceiveFromAny(i) ==
  \E S \subseteq (sent \cup ByzMsgs) : rcvd' = [ rcvd EXCEPT ![i] = rcvd[i] \cup S ]

(* Step: receive, then possibly send ECHO (a correct process sends at most one). *)
Step(i) ==
  /\ ReceiveFromAny(i)
  /\ \/ (pc[i] = "V1" /\ pc' = [pc EXCEPT ![i] = "SE"]
                              /\ sent' = sent \cup { << i, "ECHO" >> })
     \/ (pc[i] \notin { "V0", "V1" } /\ Cardinality(rcvd'[i]) >= N - 2 * T
                              /\ Cardinality(rcvd'[i]) < N - T
                              /\ pc' = [pc EXCEPT ![i] = "SE"]
                              /\ sent' = sent \cup { << i, "ECHO" >> })
     \/ (pc[i] \in { "V0", "V1" } /\ Cardinality(rcvd'[i]) >= N - T
                              /\ pc' = [pc EXCEPT ![i] = "AC"]
                              /\ sent' = sent \cup { << i, "ECHO" >> })
     \/ (pc[i] = "SE" /\ Cardinality(rcvd'[i]) >= N - T
                              /\ pc' = [pc EXCEPT ![i] = "AC"])
  /\ UNCHANGED << Corr, Faulty >>

Next == \/ \E i \in Corr : Step(i) \/ UNCHANGED vars

Spec == Init /\ [][Next]_vars
        /\ WF_vars(\E i \in Corr : ReceiveFromCorrect(i)
                              /\ (pc[i] = "V1" \/ pc[i] \notin { "V0", "V1", "SE" }
                                   \/ Cardinality(rcvd[i]) >= N - T)))

TypeOK == /\ pc \in [ Proc -> {"V0", "V1", "SE", "AC"} ]
          /\ sent \subseteq Proc \times M
          /\ Corr \subseteq Proc /\ Faulty \subseteq Proc
          /\ rcvd \in [ Proc -> SUBSET (sent \cup ByzMsgs) ]

(* FCConstraints are the semantic constraints on Corr, Faulty and ByzMsgs; they are
   used in the inductive invariant and in a separate semantic check, and are
   independent of InitNoBcast (so they are invariant even for the unrestricted
   system).  *)
FCConstraints == /\ Corr \cup Faulty = Proc
                 /\ Faulty = Proc \ Corr
                 /\ Cardinality(Corr) >= N - T
                 /\ Cardinality(Faulty) <= T
                 /\ ByzMsgs \subseteq Proc \X M
                 /\ Cardinality(ByzMsgs) = Cardinality(Faulty)

(* The special case: if no correct process broadcasts, then no correct process accepts. *)
Unforg == (\A i \in Corr : pc[i] = "V0") => [](\A i \in Corr : pc[i] # "AC")

(* The inductive invariant that implies Unforgeability.  It is the full unforgeable
   state (pc = "V0" and sent = {}) plus the semantic constraints. *)
IndInv == FCConstraints /\ TypeOK /\ sent = {} /\ pc = [ i \in Proc |-> "V0" ]

=============================================================================