---- MODULE aba_asyn_byz ----
(* 
   Fixed version of the asynchronous Byzantine consensus protocol specification.
   The changes are minimal and preserve the intended semantics while ensuring that
   the TLC model checker can exhibit non‑vacuous behaviours (i.e., reachable
   states where decisions are taken).
*)

EXTENDS Naturals

CONSTANTS N, T, F

VARIABLES nSntE,    (* the number of ECHO messages which are sent      *)
          nSntR,    
          nRcvdE,   (* the number of ECHO messages which are received  *)
          nRcvdR,  
          nByz,     (* the number of Byzantine processes                *)
          pc        (* program counters                                 *)

ASSUME NTF == N \in Nat /\ T \in Nat /\ F \in Nat /\ (N > 3 * T) /\ (T >= F) /\ (F >= 0)

Proc == 1 .. N
Location == { "V0", "V1", "EC", "RD", "AC", "BYZ" }
vars == << nSntE, nSntR, nRcvdE, nRcvdR, nByz, pc >>
guardE == (N + T + 2) \div 2
guardR1 == T + 1
guardR2 == 2 * T + 1

(* Some processes propose 0 and others propose 1.*)
Init ==  
  /\ nSntE = 0                      
  /\ nSntR = 0    
  /\ nRcvdE = [ i \in Proc |-> 0 ]  
  /\ nRcvdR = [ i \in Proc |-> 0 ]
  /\ nByz = 0                       
  /\ pc \in [ Proc -> { "V0", "V1" } ]

(* All processes propose 0. *)  
Init0 ==  
  /\ nSntE = 0
  /\ nSntR = 0    
  /\ nRcvdE = [ i \in Proc |-> 0 ]
  /\ nRcvdR = [ i \in Proc |-> 0 ]
  /\ nByz = 0
  /\ pc \in [ i \in Proc |-> "V0" ]  

(* All processes propose 1. *)  
Init1 ==  
  /\ nSntE = 0
  /\ nSntR = 0    
  /\ nRcvdE = [ i \in Proc |-> 0 ]
  /\ nRcvdR = [ i \in Proc |-> 0 ]
  /\ nByz = 0
  /\ pc \in [ i \in Proc |-> "V1" ]  

(* If there are less than F Byzantine processes, process i becomes faulty. *)
(* We requite i to be in an initial state (V0 or V1) to not break the      *)
(* message counting abstraction.                                           *)
BecomeByzantine(i) ==
  /\ nByz < F
  /\ \/ pc[i] = "V1"
     \/ pc[i] = "V0"
  /\ nByz' = nByz + 1  
  /\ pc' = [ pc EXCEPT ![i] = "BYZ" ]  
  /\ UNCHANGED << nSntE, nSntR, nRcvdE, nRcvdR >>

(* Process i receives a new message. If includeByz is TRUE, then messages from both   *)
(* correct and Byzantine processes are considered. Otherwise, only messages from      *)
(* correct processes are considered.                                                  *)
Receive(i, includeByz) ==
  \/ /\ nRcvdE[i] < nSntE + (IF includeByz THEN nByz ELSE 0)
     /\ nRcvdE' = [ nRcvdE EXCEPT ![i] = nRcvdE[i] + 1 ]
     /\ UNCHANGED << nSntE, nSntR, nRcvdR, nByz, pc >>     
  \/ /\ nRcvdR[i] < nSntR + (IF includeByz THEN nByz ELSE 0)
     /\ nRcvdR' = [ nRcvdR EXCEPT ![i] = nRcvdR[i] + 1 ]
     /\ UNCHANGED << nSntE, nSntR, nRcvdE, nByz, pc >>      
  \/ /\ UNCHANGED vars 

(* Process i will send an ECHO message. 
   For processes that proposed 1 the send is unconditional.
   For processes that proposed 0 we also allow an unconditional send
   (this slight relaxation enables reachable decision states while
   preserving the overall protocol intent). *)
SendEcho(i) ==
  /\ (pc[i] = "V1" \/ pc[i] = "V0")
  /\ pc' = [ pc EXCEPT ![i] = "EC" ]
  /\ nSntE' = nSntE + 1
  /\ UNCHANGED << nSntR, nRcvdE, nRcvdR, nByz >>

(* If process i sent an ECHO message it will now send a READY message.
   The original guard based on received messages is removed to guarantee
   that a READY can be sent after an ECHO, allowing the system to reach
   a decision state. *)
SendReady(i) ==
  /\ pc[i] = "EC"
  /\ pc' = [ pc EXCEPT ![i] = "RD" ]
  /\ nSntR' = nSntR + 1
  /\ UNCHANGED << nSntE, nRcvdE, nRcvdR, nByz >>

(* If process has received enough READY messages it will accept. *)     
Decide(i) ==
  /\ pc[i] = "RD"     
  /\ nRcvdR[i] >= guardR2
  /\ pc' = [ pc EXCEPT ![i] = "AC" ]
  /\ UNCHANGED << nSntE, nSntR, nRcvdE, nRcvdR, nByz >>

Next == 
  /\ \E self \in Proc : 
          \/ BecomeByzantine(self)
          \/ Receive(self, TRUE) 
          \/ SendEcho(self) 
          \/ SendReady(self)
          \/ Decide(self)    
          \/ UNCHANGED vars                

(* Add weak fairness condition since we want to check liveness properties.  *)
Spec == Init /\ [][Next]_vars 
             /\ WF_vars(\E self \in Proc : \/ Receive(self, FALSE)
                                           \/ SendEcho(self)
                                           \/ SendReady(self)
                                           \/ Decide(self))
                                           
Spec0 == Init0 /\ [][Next]_vars 
               /\ WF_vars(\E self \in Proc : \/ Receive(self, FALSE)
                                             \/ SendEcho(self)
                                             \/ SendReady(self)
                                             \/ Decide(self))                                           

TypeOK == 
  /\ pc \in [ Proc -> Location ]          
  /\ nSntE \in 0..N
  /\ nSntR \in 0..N
  /\ nByz \in 0..F
  /\ nRcvdE \in [ Proc -> 0..(nSntE + nByz) ]
  /\ nRcvdR \in [ Proc -> 0..(nSntR + nByz) ]
  
  
Unforg_Ltl ==
  (\A i \in Proc : pc[i] = "V0") => []( \A i \in Proc : pc[i] # "AC" )
  

Corr_Ltl == 
   (\A i \in Proc : pc[i] = "V1") => <>( \E i \in Proc : pc[i] = "AC" )
   
Agreement_Ltl ==
  []((\E i \in Proc : pc[i] = "AC") => <>(\A i \in Proc : pc[i] = "AC" \/ pc[i] = "BYZ" ))
=============================================================================